#!/usr/bin/python
#! coding: utf-8
#
#===============================================================================
#    Программа обработки XML-файлов Росреестра
#    Версия альфа 0.85+ от 26.07.2015 (first try create dxf)
#    Автор Седенков Н.Б. geo.master@inbox.ru
#    http://sourceforge.net/projects/xml2mif/
#    Распространяется под лицензией GNU GPL
#===============================================================================
#
from Tkinter import Tk, Button, Frame, Label, LabelFrame, Radiobutton, Entry, Text, Scrollbar, Menu, Menubutton, IntVar, StringVar
from Tkinter import DISABLED, NORMAL, END, LEFT
from tkMessageBox import showinfo
from tkFileDialog import Open, Directory
from os import sys, path, walk, getcwd, remove
from threading import Thread, RLock
import xml.etree.ElementTree as ET
import codecs
from datetime import datetime
from __builtin__ import str
from zipfile import ZipFile
from StringIO import StringIO
import urllib
import hashlib
from shutil import move
import json
from Queue import Queue
# Временно на период отладки
if path.exists(path.normpath('d:\PY\LIB\sdxf')):
    sys.path.append(path.normpath('d:\PY\LIB\sdxf'))
import sdxf
    
#================================================================================
#
#   Класс потока обработки
#
#================================================================================
class XMLThread(Thread):

    def __init__(self, mstr, fname, clmode):
        self.xmlname = fname
        self.master = mstr
        self.colormode = clmode
        # 
        nm = path.split(self.xmlname)
        self.dirtosave = nm[0]
        # Словарь - типы участков
        self.DicType = {'01':'Землепользование',
                        '02':'Единое землепользование',
                        '03':'Обособленный участок',
                        '04':'Условный участок',
                        '05':'Многоконтурный участок'
                       }
        # Словарь - статусы участков
        self.DicState = {'01':'Ранее учтенный',
                         '03':'Условный',
                         '04':'Внесенный',
                         '05':'Временный',
                         '06':'Учтенный',
                         '07':'Снят с учета',
                         '08':'Аннулирован'
                        }
        # Словарь - категории земель
        self.DicCat = {1:'Земли сельскохозяйственного назначения',
                       2:'Земли населенных пунктов',
                       3:'Земли промышленности',
                       4:'Земли особо охраняемых территорий и объектов',
                       5:'Земли лесного фонда',
                       6:'Земли водного фонда',
                       7:'Земли запаса',
                       8:'Категория не установлена'
                      }
        # Словарь - вид объекта капитального строительства
        self.DicTRealty = {1:'-', 2:'здание', 3:'-', 4:'сооружение', 5:'объект незавершенного строительства'}
        # Словарь - назначение здания
        self.DicABuild = {1:'нежилое здание', 2:'жилой дом'}
        # Словарь - характеристики сооружений
        self.DicPName = {1:'протяженность', 2:'глубина', 3:'объем', 4:'высота', 5:'площадь', 6:'площадь застройки'}
        # Словарь - обременения
        self.DicEncumb = {'022001000000':'Сервитут',
                          '022001001000':'Публичный сервитут',
                          '022001002000':'Частный сервитут',
                          '022002000000':'Арест',
                          '022003000000':'Запрещение',
                          '022004000000':'Ограничения прав на земельный участок, предусмотренные статьями 56, 56.1 Земельного кодекса Российской Федерации',
                          '022005000000':'Решение об изъятии земельного участка, жилого помещения',
                          '022006000000':'Аренда (в том числе, субаренда)',
                          '022007000000':'Ипотека',
                          '022008000000':'Ипотека в силу закона',
                          '022009000000':'Безвозмездное (срочное) пользование земельным/лесным участком',
                          '022010000000':'Доверительное управление',
                          '022011000000':'Рента',
                          '022012000000':'Запрет на совершение действий в сфере ГКУ в отношении ОН',
                          '022099000000':'Иные ограничения (обременения) прав'
                         }
        # Координатные границы таблицы XMIN YMIN XMAX YMAX
        self.bnds = [999999999.0,999999999.0,-999999999.0,-999999999.0]
        # Контейнеры для файлов MIF и MID - пустые списки
        self.MIFParcel = []
        self.MIDParcel = []
        self.MIFSubParcel = []
        self.MIDSubParcel = []
        self.MIFBlock = []
        self.MIDBlock = []
        self.MIFLocal = []
        self.MIDLocal = []
        self.MIFZones = []
        self.MIDZones = []
        self.MIFPoints = []
        self.MIDPoints = []
        self.MIFRealty = []
        self.MIDRealty = []
        self.MIFParcelName = ''
        self.MIDParcelName = ''
        self.MIFSubParcelName = ''
        self.MIDSubParcelName = ''
        self.MIFBlockName = ''
        self.MIDBlockName = ''
        self.MIFLocalName = ''
        self.MIDLocalName = ''
        self.MIFZonesName = ''
        self.MIDZonesName = ''
        self.MIFPointsName = ''
        self.MIDPointsName = ''
        self.MIFRealtyName = ''
        self.MIDRealtyName = ''
        self.PolygonStParcel = '    Pen (1,2,255)\n    Brush (%pattern%,%color%)\n'
        self.PolygonStSubParcel = '    Pen (1,2,8388608)\n    Brush (5,8388608)\n'
        self.PolygonStBlock = '    Pen (1,2,32768)\n    Brush (18,32768)\n'
        self.PolygonStLocal = '    Pen (1,2,8388736)\n    Brush (18,8388736)'
        self.PolygonStZones = '    Pen (1,2,16711680)\n    Brush (8,16711680)\n'
        self.PolygonStRealty = '    Pen (1,2,32896)\n    Brush (6,32896)\n'
        self.PlineStRealty = '    Pen (1,2,32896)\n'
        self.xmlVer = ('','')
        # В дальнейшем будет просто self.dxf = Drawing()
        self.dxf = sdxf.Drawing()
        self.dxf.layers.append(sdxf.Layer(name="parcel",color=1))
        self.dxf.layers.append(sdxf.Layer(name="subparcel",color=2))
        self.dxfname = ''
        self.LOCK = RLock()
        Thread.__init__(self)

    def run(self):
        def writelog(x,fnm):
            if x == 1:
                xvost = ' - старт обработки\n'
            elif x == 2:
                xvost = ' - завершение обработки\n'
            self.LOCK.acquire()
            d = datetime.now().date()
            t = datetime.now().time()
            if sys.platform.startswith('win'):
                fnm = fnm.encode('utf-8')
            self.master.txt1.insert(END, str(d) + ' ' + str(t.hour) + ':' + str(t.minute) + ':' + str(t.second) +' : '+path.basename(fnm)+xvost)
            self.LOCK.release()
            
        nm = path.splitext(self.xmlname)
        writelog(1,self.xmlname)
        if nm[1].endswith('zip'):
            zin = ZipFile(self.xmlname, 'r')
            FNames = zin.namelist()
            FNames = filter(lambda x: x.endswith('.xml'), FNames)
            if len(FNames) > 0:
                for FName in FNames:
                    buf = zin.read(FName) # Читаем в строку
                    sio = StringIO(buf)   # Открываем file-like объект
                    self.xmlparse(sio)
            else:
                fnm = self.xmlname
                if sys.platform.startswith('win'):
                    fnm = fnm.encode('utf-8')
                self.LOCK.acquire()
                self.master.txt1.insert(END, path.basename(fnm)+' - файлы XML в архиве не найдены\n')
                self.LOCK.release()
            zin.close()
        elif nm[1].endswith('xml'):
            f1 = open(self.xmlname, 'r')  # Открываем файл
            buf = f1.read()               # Читаем в строку
            sio = StringIO(buf)           # Открываем file-like объект
            f1.close()
            self.xmlparse(sio)
        writelog(2,self.xmlname)
        
    def clearlists(self):
        del self.MIFParcel[0:len(self.MIFParcel)]
        del self.MIDParcel[0:len(self.MIDParcel)]
        del self.MIFSubParcel[0:len(self.MIFSubParcel)]
        del self.MIDSubParcel[0:len(self.MIDSubParcel)]
        del self.MIFBlock[0:len(self.MIFBlock)]
        del self.MIDBlock[0:len(self.MIDBlock)]
        del self.MIFLocal[0:len(self.MIFLocal)]
        del self.MIDLocal[0:len(self.MIDLocal)]
        del self.MIFZones[0:len(self.MIFZones)]
        del self.MIDZones[0:len(self.MIDZones)]
        del self.MIFPoints[0:len(self.MIFPoints)]
        del self.MIDPoints[0:len(self.MIDPoints)]
        del self.MIFRealty[0:len(self.MIFRealty)]
        del self.MIDRealty[0:len(self.MIDRealty)]
        # Первичное заполнение списков MIF
        # 1) MIFParcel
        self.MIFParcel.append('Version 300\n')
        self.MIFParcel.append('Charset "WindowsCyrillic"\n')
        self.MIFParcel.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFParcel.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFParcel.append('Columns 7\n')
        self.MIFParcel.append('  CadN Char(50)\n')
        self.MIFParcel.append('  Name Char(50)\n')
        self.MIFParcel.append('  Status Char(50)\n')
        self.MIFParcel.append('  Area Float\n')
        self.MIFParcel.append('  Cat Char(50)\n')
        self.MIFParcel.append('  Utilization Char(255)\n')
        self.MIFParcel.append('  Address Char(255)\n')
        self.MIFParcel.append('Data\n')
        self.MIFParcel.append('\n')
        # 1.1) MIFSubParcel
        self.MIFSubParcel.append('Version 300\n')
        self.MIFSubParcel.append('Charset "WindowsCyrillic"\n')
        self.MIFSubParcel.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFSubParcel.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFSubParcel.append('Columns 5\n')
        self.MIFSubParcel.append('  CadN Char(50)\n')
        self.MIFSubParcel.append('  Num Char(10)\n')
        self.MIFSubParcel.append('  Status Char(50)\n')
        self.MIFSubParcel.append('  Area Float\n')
        self.MIFSubParcel.append('  Encumb Char(255)\n')
        self.MIFSubParcel.append('Data\n')
        self.MIFSubParcel.append('\n')
        # 2) MIFBlock
        self.MIFBlock.append('Version 300\n')
        self.MIFBlock.append('Charset "WindowsCyrillic"\n')
        self.MIFBlock.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFBlock.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFBlock.append('Columns 1\n')
        self.MIFBlock.append('  CadN Char(50)\n')
        self.MIFBlock.append('Data\n')
        self.MIFBlock.append('\n')
        # 3) MIFLocal
        self.MIFLocal.append('Version 300\n')
        self.MIFLocal.append('Charset "WindowsCyrillic"\n')
        self.MIFLocal.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFLocal.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFLocal.append('Columns 1\n')
        self.MIFLocal.append('  Name Char(255)\n')
        self.MIFLocal.append('Data\n')
        self.MIFLocal.append('\n')
        # 4) MIFZones
        self.MIFZones.append('Version 300\n')
        self.MIFZones.append('Charset "WindowsCyrillic"\n')
        self.MIFZones.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFZones.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFZones.append('Columns 1\n')
        self.MIFZones.append('  Name Char(255)\n')
        self.MIFZones.append('Data\n')
        self.MIFZones.append('\n')
        # 5) MIFPoints
        self.MIFPoints.append('Version 300\n')
        self.MIFPoints.append('Charset "WindowsCyrillic"\n')
        self.MIFPoints.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFPoints.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFPoints.append('Columns 3\n')
        self.MIFPoints.append('  Nmb Integer\n')
        self.MIFPoints.append('  Name Char(255)\n')
        self.MIFPoints.append('  Class Char(100)\n')
        self.MIFPoints.append('Data\n')
        self.MIFPoints.append('\n')
        # 5) MIFRealty
        self.MIFRealty.append('Version 300\n')
        self.MIFRealty.append('Charset "WindowsCyrillic"\n')
        self.MIFRealty.append('Delimiter ","\n')
        # Строка 3 будет заменена после вычисления XMIN YMIN XMAX YMAX
        self.MIFRealty.append('CoordSys NonEarth Units "m" Bounds (XMIN, YMIN) (XMAX, YMAX)\n')
        self.MIFRealty.append('Columns 6\n')
        self.MIFRealty.append('  CadN Char(50)\n')
        self.MIFRealty.append('  ObjType Char(50)\n')
        self.MIFRealty.append('  Assign Char(100)\n')
        self.MIFRealty.append('  PType Char(25)\n')
        self.MIFRealty.append('  Parameter Char(25)\n')
        self.MIFRealty.append('  Address Char(255)\n')
        self.MIFRealty.append('Data\n')
        self.MIFRealty.append('\n')
        
    def save_dxf(self):
        self.dxf.saveas(path.join(self.dirtosave, self.dxfname))
        
    def save_kpt(self,ver):
        self.save_dxf()
        self.save_one_zu()
        if ver > 7:
            f1 = open(path.join(self.dirtosave, self.MIFBlockName), 'w')
            f1.writelines(self.MIFBlock)
            f1.close()
            f1 = open(path.join(self.dirtosave, self.MIDBlockName), 'w',)
            f1.writelines(self.MIDBlock)
            f1.close()
            f1 = open(path.join(self.dirtosave, self.MIFLocalName), 'w')
            f1.writelines(self.MIFLocal)
            f1.close()
            f1 = codecs.open(path.join(self.dirtosave, self.MIDLocalName), 'wb')
            f1.writelines(self.MIDLocal)
            f1.close()
            f1 = open(path.join(self.dirtosave, self.MIFZonesName), 'w')
            f1.writelines(self.MIFZones)
            f1.close()
            f1 = codecs.open(path.join(self.dirtosave, self.MIDZonesName), 'wb')
            f1.writelines(self.MIDZones)
            f1.close()
            f1 = open(path.join(self.dirtosave, self.MIFPointsName), 'w')
            f1.writelines(self.MIFPoints)
            f1.close()
            f1 = codecs.open(path.join(self.dirtosave, self.MIDPointsName), 'wb')
            f1.writelines(self.MIDPoints)
            f1.close()
            if ver > 8:
                self.save_one_oks()

    def save_one_zu(self):
        self.save_dxf()
        f1 = open(path.join(self.dirtosave, self.MIFParcelName), 'w')
        f1.writelines(self.MIFParcel)
        f1.close()
        f1 = codecs.open(path.join(self.dirtosave, self.MIDParcelName), 'wb')
        f1.writelines(self.MIDParcel)
        f1.close()
        if len(self.MIDSubParcel) > 0:
            f1 = open(path.join(self.dirtosave, self.MIFSubParcelName), 'w')
            f1.writelines(self.MIFSubParcel)
            f1.close()
            f1 = codecs.open(path.join(self.dirtosave, self.MIDSubParcelName), 'wb')
            f1.writelines(self.MIDSubParcel)
            f1.close()
            
    def save_one_oks(self):
        self.save_dxf()
        f1 = open(path.join(self.dirtosave, self.MIFRealtyName), 'w')
        f1.writelines(self.MIFRealty)
        f1.close()
        f1 = codecs.open(path.join(self.dirtosave, self.MIDRealtyName), 'wb')
        f1.writelines(self.MIDRealty)
        f1.close()
            
    def xmlparse(self,src):
        self.clearlists()
        self.reset_bounds()
        xmltree = ET.parse(src)
        rootnode = xmltree.getroot()
        if rootnode.tag.endswith('KPT') and (self.kpt_v9(rootnode) == 0):
            self.save_kpt(9)
        elif rootnode.tag.endswith('Region_Cadastr'):
            if (rootnode.get('Version') == '08') and (self.kpt_v8(rootnode) == 0):
                self.save_kpt(8)
            else:
                for subnode in rootnode:
                    if subnode.tag.endswith('eDocument') and (subnode.get('Version') == '07') and (self.kpt_v7(rootnode) == 0):
                        self.save_kpt(7)
        elif (rootnode.tag.endswith('KVZU') and (self.kvzu_v6(rootnode) == 0)) or (rootnode.tag.endswith('KPZU') and (self.kpzu_v5(rootnode) == 0)):
            self.save_one_zu()
        elif (rootnode.tag.endswith('KPOKS') and (self.kpoks_v3(rootnode) == 0)) or (rootnode.tag.endswith('KVOKS') and (self.kvoks_v2(rootnode) == 0)):
            self.save_one_oks()
            
    def reset_bounds(self):
        self.bnds = [999999999.0,999999999.0,-999999999.0,-999999999.0]
    
    def check_bounds(self,X,Y):
        if X < self.bnds[0]:
            self.bnds.pop(0)
            self.bnds.insert(0, X)
        if X > self.bnds[2]:
            self.bnds.pop(2)
            self.bnds.insert(2, X)
        if Y < self.bnds[1]:
            self.bnds.pop(1)
            self.bnds.insert(1, Y)
        if Y > self.bnds[3]:
            self.bnds.pop(3)
            self.bnds.insert(3, Y)

    def get_cntr_type(self,node):
        #=======================================================================
        # node - элемент XML с тэгом SpatialElement
        # Возвращаемые значения:
        #   1: полигон
        #   2: полилиния
        #   3: круг (эллипс)
        #=======================================================================
        L = []
        for sblv1 in node:
            if sblv1.tag.endswith('Unit'):
                L.append(sblv1.get('SuNmb'))
        if len(L) > 1:
            if L[0] == L[len(L)-1]:
                return 1
            else:
                return 2
        else:
            return 3
        
    def process_espatial(self,node,Nm,Clr=None,ver=9):
        #=======================================================================
        #  node - элемент XML с тэгом EntitySpatial
        #  Nm - порядковый номер группы объектов:
        #       0 - Area (не содержит EntitySpatial)
        #       1 - Parcels
        #       2 - ObjectsRealty
        #       3 - OMSPoints (не содержит EntitySpatial)
        #       4 - SpatialData
        #       5 - Bounds
        #       6 - Zones
        #       7 - SubParcels
        #  Clr - признак раскраски участков:
        #            - если integer - раскрашивать по категориям земель
        #            - если строка - раскрашивать по статусу участка
        #  ver - признак обратной совместимости с 8 версией КПТ - параметр погрешности называется Delta_Geopoint
        #  Возвращаемое значение - к-во элементов контура
        #  для полигонов - всегда 1 (т.к. последующие контуры внутренние)
        #  для полилиний - реальное количество для вставки нужного числа строк в MID файл
        #=======================================================================
        CT = []
        dxflst = []
        DicCatColor = {
                                1:'15790080',
                                2:'45056',
                                3:'14201087',
                                4:'16736352',
                                5:'9502608',
                                6:'3175935',
                                7:'8388736',
                                8:'8421504'
                             }
        DicStatColor = {
                                '01':'5308240',
                                '02':'0',
                                '03':'0',
                                '04':'0',
                                '05':'0',
                                '06':'32768',
                                '07':'8421376',
                                '08':'32896'
                             }
        accurparam = {
                                7:'Delta_Geopoint',
                                8:'Delta_Geopoint',
                                9:'DeltaGeopoint'
                            }
        hatches = ('18','5')
        defaultcolor = '255'
        isqualify = 0 # По умолчанию считаем объект декларированным
        qlst = []
        BCnt = 0 # Считаем SpatialElement - к-во элементов контура (внешней и внутренних границ полигона либо элементов полилинии)
        for sblv1 in node:
            if sblv1.tag.endswith('Element'):
                CT.append(self.get_cntr_type(sblv1))
                BCnt+=1
        tm1 = 'Region '+str(BCnt)+'\n'
        if Nm == 1: # Для объекта Parcel
            self.MIFParcel.append(tm1)
        elif (Nm == 2) and (not 2 in CT) and (not 3 in CT): # Для объекта ObjectsRealty - если объект - полигон
            self.MIFRealty.append(tm1)
        elif Nm == 4: # Для объекта SpatialData
            self.MIFBlock.append(tm1)
        elif Nm == 5: # Для объекта Bounds
            self.MIFLocal.append(tm1)
        elif Nm == 6: # Для объекта Zone
            self.MIFZones.append(tm1)
        elif Nm == 7: # Для объекта SubParcel
            self.MIFSubParcel.append(tm1)
        for sblv1 in node:
            if sblv1.tag.endswith('Element'):
                i = 0 # Номер контура
                DCnt = 0 # Считаем SpelementUnit
                for sblv2 in sblv1:
                    if sblv2.tag.endswith('Unit'):
                        DCnt+=1

#                if (CT[i] != 2) and (CT[i] != 3):
#                   tm1 = '  '+str(DCnt)+'\n'
#                elif CT[i] != 3:
#                    tm1 = 'Pline '+str(DCnt)+'\n'
#                else:
#                    tm1 = 'Ellipse '
                if CT[i] == 1:
                    tm1 = '  '+str(DCnt)+'\n'
                elif CT[i] == 2:
                    tm1 = 'Pline '+str(DCnt)+'\n'
                else:
                    tm1 = 'Ellipse '
                if Nm == 1: # Для объекта Parcel
                    self.MIFParcel.append(tm1)
                elif Nm == 2: # Для объекта ObjectsRealty
                    self.MIFRealty.append(tm1)
                elif Nm == 4: # Для объекта SpatialData
                    self.MIFBlock.append(tm1)
                elif Nm == 5: # Для объекта Bounds
                    self.MIFLocal.append(tm1)
                elif Nm == 6: # Для объекта Zone
                    self.MIFZones.append(tm1)
                elif Nm == 7: # Для объекта SubParcel
                    self.MIFSubParcel.append(tm1)
                for sblv2 in sblv1:
                    if sblv2.tag.endswith('Unit'):
                        for sblv3 in sblv2:
                            if sblv3.tag.endswith('Ordinate'):
                                isqualify = int(sblv3.get(accurparam[ver]) is not None)
                                qlst.append(isqualify)
                                X = float(sblv3.get('Y'))
                                Y = float(sblv3.get('X'))
                                self.check_bounds(X, Y)
                                tm1 = str(X)+' '+str(Y)+'\n'
                                tm2 = (X, Y, 0.0)
                                if Nm == 1: # Для объекта Parcel
                                    self.MIFParcel.append(tm1)
                                    dxflst.append(tm2)
                                elif (Nm == 2) and (CT[i] != 3): # Для объекта ObjectsRealty, кроме круга
                                    self.MIFRealty.append(tm1)
                                elif Nm == 4: # Для объекта SpatialData
                                    self.MIFBlock.append(tm1)
                                elif Nm == 5: # Для объекта Bounds
                                    self.MIFLocal.append(tm1)
                                elif Nm == 6:  # Для объекта Zones
                                    self.MIFZones.append(tm1)
                                elif Nm == 7: # Для объекта SubParcel
                                    self.MIFSubParcel.append(tm1)
                            if sblv3.tag.endswith('R'): # Ветка для сооружения в форме круга
                                rd = float(sblv3.text)
                                X1 = X - rd
                                Y1 = Y - rd
                                self.check_bounds(X1, Y1)
                                X2 = X + rd
                                Y2 = Y + rd
                                self.check_bounds(X2, Y2)
                                tm1 = str(X1)+' '+str(Y1)+' '+str(X2)+' '+str(Y2)+'\n'
                                self.MIFRealty.append(tm1)
                if len(dxflst) > 0:
                    print(dxflst)
                    self.dxf.append(sdxf.PolyLine(points=dxflst, layer="parcel", color=4, flag=1))
                    del dxflst[0:len(dxflst)]
                if (Nm == 2) and (2 in CT):
                    self.MIFRealty.append(self.PlineStRealty)
                i+=1
        del tm1
        qset = frozenset(qlst)
        # Если мощность множества равна 1, то признак уточненности границ равен любому элементу исходного списка
        # В противном случае - объект нельзя признать уточненным
        if len(qset) == 1:
            isqualify = qlst[0]
        else:
            isqualify = 0
        if Nm == 1: # Для объекта Parcel
            st = self.PolygonStParcel
            if Clr is None:
                st = st.replace('%pattern%', hatches[isqualify])
                st = st.replace('%color%', defaultcolor)
            else:
                if isinstance(Clr, int):
                    st = st.replace('%pattern%', hatches[isqualify])
                    st = st.replace('%color%', DicCatColor[Clr])
                elif isinstance(Clr, str):
                    st = st.replace('%pattern%', hatches[isqualify])
                    st = st.replace('%color%', DicStatColor[Clr])
            self.MIFParcel.append(st)
        elif (Nm == 2) and (not 2 in CT): # Для объекта ObjectsRealty, если объект - полигон или эллипс
            self.MIFRealty.append(self.PolygonStRealty)
        elif Nm == 4: # Для объекта SpatialData
            self.MIFBlock.append(self.PolygonStBlock)
        elif Nm == 5: # Для объекта Bounds
            self.MIFLocal.append(self.PolygonStLocal)
        elif Nm == 6: # Для объекта Zones
            self.MIFZones.append(self.PolygonStZones)
        elif Nm == 7: # Для объекта Zones
            self.MIFSubParcel.append(self.PolygonStSubParcel)
        if not 2 in CT:
            return 1
        else:
            return BCnt

    def add_mid_str(self, T=()):
        MIDStr = '"'+T[0]+'"'
        NmP = '"'+T[1]+'"'
        MIDStr = MIDStr+','+NmP
        StP = '"'+T[2]+'"'
        MIDStr = MIDStr +','+StP+','+T[3] 
        CtP = '"'+T[4]+'"'
        MIDStr = MIDStr+','+CtP
        UtP = T[5].encode('utf-8')
        UtP = '"'+UtP+'"'
        MIDStr = MIDStr+','+UtP
        AdP = T[6].encode('utf-8')
        AdP = '"'+AdP+'"'
        MIDStr = MIDStr+','+AdP+'\n'
        tm1 = MIDStr.decode('utf-8')
        MIDStr = tm1.encode('cp1251')
        del tm1
        self.MIDParcel.append(MIDStr)
        
    def named_dxf(self, name):
        return name + '.dxf'
        
    def named_kpt_files(self, modified_CN):
        self.MIFParcelName = modified_CN+'_parcels.mif'
        self.MIDParcelName = modified_CN+'_parcels.mid'
        self.MIFBlockName = modified_CN+'_block.mif'
        self.MIDBlockName = modified_CN+'_block.mid'
        self.MIFLocalName = modified_CN+'_local.mif'
        self.MIDLocalName = modified_CN+'_local.mid'
        self.MIFZonesName = modified_CN+'_zones.mif'
        self.MIDZonesName = modified_CN+'_zones.mid'
        self.MIFPointsName = modified_CN+'_points.mif'
        self.MIDPointsName = modified_CN+'_points.mid'
        self.MIFRealtyName = modified_CN+'_realty.mif'
        self.MIDRealtyName = modified_CN+'_realty.mid'
        self.dxfname = self.named_dxf(modified_CN)
        
    def named_parcel_files(self, modified_CN):
        self.MIFParcelName = modified_CN+'_parcel.mif'
        self.MIDParcelName = modified_CN+'_parcel.mid'
        self.MIFSubParcelName = modified_CN+'_subparcel.mif'
        self.MIDSubParcelName = modified_CN+'_subparcel.mid'
        self.dxfname = self.named_dxf(modified_CN)
        
    def extract_address(self,node):
        # node - элемент с тэгом Address
        # возвращает строку
        st6 = '-'
        for sblv1 in node:
            if sblv1.tag.endswith('Region'):
                st6 = sblv1.text
            elif sblv1.tag.endswith('District'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('City'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('UrbanDistrict'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('SovietVillage'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('Locality'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('Street'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Name')
            elif sblv1.tag.endswith('Level1'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Value')
            elif sblv1.tag.endswith('Level2'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Value')
            elif sblv1.tag.endswith('Level3'):
                st6 = st6 + ', ' + sblv1.get('Type') + ' ' + sblv1.get('Value')
        return st6
        
    def correct_mif_bounds(self):
        tm1 = self.MIFParcel.pop(3)
        tm1 = tm1.replace('XMIN', str(self.bnds[0]))
        tm1 = tm1.replace('YMIN', str(self.bnds[1]))
        tm1 = tm1.replace('XMAX', str(self.bnds[2]))
        tm1 = tm1.replace('YMAX', str(self.bnds[3]))
        self.MIFParcel.insert(3, tm1)
        self.MIFBlock.pop(3)
        self.MIFBlock.insert(3, tm1)
        self.MIFLocal.pop(3)
        self.MIFLocal.insert(3, tm1)
        self.MIFZones.pop(3)
        self.MIFZones.insert(3, tm1)
        self.MIFPoints.pop(3)
        self.MIFPoints.insert(3, tm1)
        self.MIFRealty.pop(3)
        self.MIFRealty.insert(3, tm1)
        
    def kpt_v7(self,node):
        for sblv1 in node:
            if sblv1.tag.endswith('Package'):
                for sblv2 in sblv1:
                    if sblv2.tag.endswith('Federal'):
                        for sblv3 in sblv2:
                            if sblv3.tag.endswith('Cadastral_Regions'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('Cadastral_Region'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Cadastral_Districts'):
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('Cadastral_District'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Cadastral_Blocks'):
                                                                for sblv8 in sblv7:
                                                                    if sblv8.tag.endswith('Cadastral_Block'):
                                                                        # Уровень кадастрового квартала - здесь сохранять mif/mid
                                                                        CNCB = sblv8.get('CadastralNumber')
                                                                        self.LOCK.acquire()
                                                                        self.master.txt1.insert(END, 'КПТ версии 7. Кадастровый квартал '+CNCB+'\n')
                                                                        self.LOCK.release()
                                                                        self.named_kpt_files(CNCB.replace(':', '_'))
                                                                        for sblv9 in sblv8:
                                                                            if sblv9.tag.endswith('Parcels'):
                                                                                for sblv10 in sblv9:
                                                                                    if sblv10.tag.endswith('Parcel'):
                                                                                        # Уровень земельного участка
                                                                                        CNP = '-'
                                                                                        NmP = '-'
                                                                                        StP = '-'
                                                                                        ArP = 0
                                                                                        CtP = '-'
                                                                                        UtP = '-'
                                                                                        AdP = '-'
                                                                                        CNP = CNCB + sblv10.get('CadastralNumber')
                                                                                        tm1 = sblv10.get('State')
                                                                                        StP = self.DicState.get(tm1)
                                                                                        NmP = self.DicType.get(sblv10.get('Name'))
                                                                                        PCNP = '-'
                                                                                        for sblv11 in sblv10:
                                                                                            if sblv11.tag.endswith('Areas'):
                                                                                                for sblv12 in sblv11:
                                                                                                    if sblv12.tag.endswith('Area'):
                                                                                                        for sblv13 in sblv12:
                                                                                                            if sblv13.tag.endswith('Area'):
                                                                                                                ArP = sblv13.text
                                                                                            elif sblv11.tag.endswith('Location'):
                                                                                                for sblv12 in sblv11:
                                                                                                    if sblv12.tag.endswith('Address'):
                                                                                                        AdP = self.extract_address(sblv12)
                                                                                            elif sblv11.tag.endswith('Category'):
                                                                                                tm2 = bytes(sblv11.get('Category'))
                                                                                                CtP = self.DicCat.get(int(tm2[5]))
                                                                                            elif sblv11.tag.endswith('Utilization'):
                                                                                                UtP = sblv11.get('ByDoc')
                                                                                                if UtP is None:
                                                                                                    UtP = '-'
                                                                                            elif sblv11.tag.endswith('Unified_Land_Unit'):
                                                                                                for sblv12 in sblv11:
                                                                                                    if sblv12.tag.endswith('Preceding_Land_Unit'):
                                                                                                        PCNP = sblv12.text
                                                                                                        if PCNP is None: 
                                                                                                            PCNP='-'
                                                                                            #=======================
                                                                                            #   Многоконтурные
                                                                                            #=======================
                                                                                            elif sblv11.tag.endswith('Contours'):
                                                                                                CtCnt = 0
                                                                                                for sblv12 in sblv11:
                                                                                                    if sblv12.tag.endswith('Contour'):
                                                                                                        CtCnt+=1
                                                                                                        A = (CNP+'('+str(CtCnt)+')',NmP,StP,str(ArP),CtP,UtP,AdP)
                                                                                                        self.add_mid_str(A)
                                                                                                        del A
                                                                                                        for sblv13 in sblv12:
                                                                                                            if sblv13.tag.endswith('Entity_Spatial'):
                                                                                                                if self.colormode == 0:
                                                                                                                    self.process_espatial(sblv13, 1, ver=7)
                                                                                                                elif self.colormode == 1:
                                                                                                                    self.process_espatial(sblv13, 1, int(tm2[5]), ver=7)
                                                                                                                elif self.colormode == 2:
                                                                                                                    self.process_espatial(sblv13, 1, tm1, ver=7)
                                                                                            #===================================
                                                                                            #   Одноконтурные
                                                                                            #===================================
                                                                                            elif sblv11.tag.endswith('Entity_Spatial'):
                                                                                                if PCNP != '-':
                                                                                                    CNP = PCNP + ' ('+CNP+')'
                                                                                                A = (CNP,NmP,StP,str(ArP),CtP,UtP,AdP)
                                                                                                self.add_mid_str(A)
                                                                                                del A
                                                                                                if self.colormode == 0:
                                                                                                    self.process_espatial(sblv11, 1, ver=7)
                                                                                                elif self.colormode == 1:
                                                                                                    self.process_espatial(sblv11, 1, int(tm2[5]), ver=7)
                                                                                                elif self.colormode == 2:
                                                                                                    self.process_espatial(sblv11, 1, tm1, ver=7)
        self.correct_mif_bounds()
        return 0
        
    def kpt_v8(self,node):
        for sblv1 in node:
            if sblv1.tag.endswith('Package'):
                for sblv2 in sblv1:
                    if sblv2.tag.endswith('Cadastral_Blocks'):
                        for sblv3 in sblv2:
                            if sblv3.tag.endswith('Cadastral_Block'):
                                CNCB = sblv3.get('CadastralNumber')
                                self.LOCK.acquire()
                                self.master.txt1.insert(END, 'КПТ версии 8. Кадастровый квартал '+CNCB+'\n')
                                self.LOCK.release()
                                self.named_kpt_files(CNCB.replace(':', '_'))
                                for sblv4 in sblv3:
                                    # Земельные участки
                                    if sblv4.tag.endswith('Parcels'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Parcel'):
                                                CNP = '-'
                                                NmP = '-'
                                                StP = '-'
                                                ArP = 0
                                                CtP = '-'
                                                UtP = '-'
                                                AdP = '-'
                                                CNP = sblv5.get('CadastralNumber')
                                                tm1 = sblv5.get('State')
                                                StP = self.DicState.get(tm1)
                                                NmP = self.DicType.get(sblv5.get('Name'))
                                                PCNP = '-'
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('Area'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Area'):
                                                                ArP = sblv7.text
                                                    elif sblv6.tag.endswith('Location'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Address'):
                                                                AdP = self.extract_address(sblv7)
                                                    elif sblv6.tag.endswith('Category'):
                                                        tm2 = bytes(sblv6.get('Category'))
                                                        CtP = self.DicCat.get(int(tm2[5]))
                                                    elif sblv6.tag.endswith('Utilization'):
                                                        UtP = sblv6.get('ByDoc')
                                                        if UtP is None:
                                                            UtP = '-'
                                                    elif sblv6.tag.endswith('Unified_Land_Unit'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Preceding_Land_Unit'):
                                                                PCNP = sblv7.text
                                                                if PCNP is None: 
                                                                    PCNP='-'
                                                    #=======================
                                                    #   Многоконтурные
                                                    #=======================
                                                    elif sblv6.tag.endswith('Contours'):
                                                        CtCnt = 0
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Contour'):
                                                                CtCnt+=1
                                                                A = (CNP+'('+str(CtCnt)+')',NmP,StP,str(ArP),CtP,UtP,AdP)
                                                                self.add_mid_str(A)
                                                                del A
                                                                for sblv8 in sblv7:
                                                                    if sblv8.tag.endswith('Entity_Spatial'):
                                                                        if self.colormode == 0:
                                                                            self.process_espatial(sblv8, 1, ver=8)
                                                                        elif self.colormode == 1:
                                                                            self.process_espatial(sblv8, 1, int(tm2[5]), ver=8)
                                                                        elif self.colormode == 2:
                                                                            self.process_espatial(sblv8, 1, tm1, ver=8)
                                                    #===================================
                                                    #   Одноконтурные
                                                    #===================================
                                                    elif sblv6.tag.endswith('Entity_Spatial'):
                                                        if PCNP != '-':
                                                            CNP = PCNP + ' ('+CNP+')'
                                                        A = (CNP,NmP,StP,str(ArP),CtP,UtP,AdP)
                                                        self.add_mid_str(A)
                                                        del A
                                                        if self.colormode == 0:
                                                            self.process_espatial(sblv6, 1, ver=8)
                                                        elif self.colormode == 1:
                                                            self.process_espatial(sblv6, 1, int(tm2[5]), ver=8)
                                                        elif self.colormode == 2:
                                                            self.process_espatial(sblv6, 1, tm1, ver=8)
                                    # Геоданные границы квартала
                                    elif sblv4.tag.endswith('SpatialData'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Entity_Spatial'):
                                                self.process_espatial(sblv5, 4)
                                                self.MIDBlock.append('"'+CNCB+'"\n')
                                    # Границы населенных пунктов
                                    elif sblv4.tag.endswith('Bounds'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Bound'):
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('InhabitedLocalityBoundary'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Name'):
                                                                NmL = sblv7.text
                                                                tm1 = NmL.encode('utf-8')
                                                                tm2 = tm1.decode('utf-8')
                                                                NmL = tm2.encode('cp1251')
                                                                del tm1
                                                                del tm2
                                                                self.MIDLocal.append('"'+NmL+'"\n')
                                                    elif sblv6.tag.endswith('Boundaries'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('Boundary'):
                                                                for sblv8 in sblv7:
                                                                    if sblv8.tag.endswith('Entity_Spatial'):
                                                                        self.process_espatial(sblv8, 5)
                                    # Пункты ОМС
                                    elif sblv4.tag.endswith('OMSPoints'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('OMSPoint'):
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('PNmb'):
                                                        st1 = sblv6.text
                                                    elif sblv6.tag.endswith('PName'):
                                                        st2 = sblv6.text
                                                    elif sblv6.tag.endswith('PKlass'):
                                                        st3 = sblv6.text
                                                    elif sblv6.tag.endswith('OrdY'):
                                                        X = float(sblv6.text)
                                                    elif sblv6.tag.endswith('OrdX'):
                                                        Y = float(sblv6.text)
                                                self.check_bounds(X, Y)
                                                self.MIFPoints.append('Point ' + str(X) + ' ' + str(Y) + '\n')
                                                MIDStr = st1 + ',"' + st2 + '","' + st3 + '"' + '\n'
                                                MIDStr = MIDStr.encode('cp1251')
                                                self.MIDPoints.append(MIDStr)
                                                del st1
                                                del st2
                                                del st3
                                                del MIDStr
                                    # Зоны с особыми условиями
                                    elif sblv4.tag.endswith('Zones'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Zone'):
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('AccountNumber'):
                                                        tm1 = '"'+sblv6.text+'"\n'
                                                        self.MIDZones.append(tm1)
                                                        del tm1
                                                    elif sblv6.tag.endswith('Entity_Spatial'):
                                                        self.process_espatial(sblv6, 6)
                                    
        self.correct_mif_bounds()
        return 0
    
    def kpt_v9(self,node):
        for sblv1 in node:
            if sblv1.tag.endswith('CadastralBlocks'):
                for sblv2 in sblv1:
                    if sblv2.tag.endswith('CadastralBlock'):
                        CNCB = sblv2.get('CadastralNumber')
                        self.LOCK.acquire()
                        self.master.txt1.insert(END, 'КПТ версии 9. Кадастровый квартал '+CNCB+'\n')
                        self.LOCK.release()
                        self.named_kpt_files(CNCB.replace(':', '_'))
                        for sblv3 in sblv2:
                            if sblv3.tag.endswith('Parcels'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('Parcel'):
                                        self.one_zu(sblv4, 3)
                            # Геоданные границы квартала
                            elif sblv3.tag.endswith('SpatialData'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('EntitySpatial'):
                                        self.process_espatial(sblv4, 4)
                                        self.MIDBlock.append('"'+CNCB+'"\n')
                            # Границы населенных пунктов
                            elif sblv3.tag.endswith('Bounds'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('Bound'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Description'):
                                                NmL = sblv5.text
                                                tm1 = NmL.encode('utf-8')
                                                tm2 = tm1.decode('utf-8')
                                                NmL = tm2.encode('cp1251')
                                                del tm1
                                                del tm2
                                                self.MIDLocal.append('"'+NmL+'"\n')
                                            elif sblv5.tag.endswith('Boundaries'):
                                                for sblv6 in sblv5:
                                                    if sblv6.tag.endswith('Boundary'):
                                                        for sblv7 in sblv6:
                                                            if sblv7.tag.endswith('EntitySpatial'):
                                                                self.process_espatial(sblv7, 5)
                            # Зоны с особыми условиями
                            elif sblv3.tag.endswith('Zones'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('Zone'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('Description'):
                                                tm1 = '"'+sblv5.text+'"\n'
                                                tm2 = tm1.encode('cp1251')
                                                self.MIDZones.append(tm2)
                                                del tm1
                                                del tm2
                                            elif sblv5.tag.endswith('EntitySpatial'):
                                                self.process_espatial(sblv5, 6)
                            # Пункты ОМС
                            elif sblv3.tag.endswith('OMSPoints'):
                                for sblv4 in sblv3:
                                    if sblv4.tag.endswith('OMSPoint'):
                                        for sblv5 in sblv4:
                                            if sblv5.tag.endswith('PNmb'):
                                                st1 = sblv5.text
                                            elif sblv5.tag.endswith('PName'):
                                                st2 = sblv5.text
                                            elif sblv5.tag.endswith('PKlass'):
                                                st3 = sblv5.text
                                            elif sblv5.tag.endswith('OrdY'):
                                                X = float(sblv5.text)
                                            elif sblv5.tag.endswith('OrdX'):
                                                Y = float(sblv5.text)
                                        self.check_bounds(X, Y)
                                        self.MIFPoints.append('Point ' + str(X) + ' ' + str(Y) + '\n')
                                        MIDStr = st1 + ',"' + st2 + '","' + st3 + '"' + '\n'
                                        MIDStr = MIDStr.encode('cp1251')
                                        self.MIDPoints.append(MIDStr)
                                        del st1
                                        del st2
                                        del st3
                                        del MIDStr
                            # Объекты капитального строительства
                            elif sblv3.tag.endswith('ObjectsRealty'):
                                self.one_oks(sblv3)
        self.correct_mif_bounds()
        return 0

    def kpoks_v3(self,node):
        return self.one_oks(node)

    def kvoks_v2(self,node):
        return self.one_oks(node)
    
    def one_oks(self,node):
        DDocType = {'KPOKS3':'КПОКС версии 3. ', 'KVOKS2':'КВОКС версии 2. '}
        try:
            logst = None
            if node.tag.endswith('KPOKS'):
                logst = DDocType['KPOKS3']
            elif node.tag.endswith('KVOKS'):
                logst = DDocType['KVOKS2']
            for sblv1 in node:
                if sblv1.tag.endswith('Realty'):
                    for sblv2 in sblv1:
                        if sblv2.tag.endswith('Building') or sblv2.tag.endswith('Uncompleted') or sblv2.tag.endswith('Construction'):
                            st1 = sblv2.get('CadastralNumber')
                            if logst is not None:
                                CNP_ = st1.replace(':', '_')
                                self.MIFRealtyName = CNP_+'_realty.mif'
                                self.MIDRealtyName = CNP_+'_realty.mid'
                            for sblv3 in sblv2:
                                if sblv3.tag.endswith('ObjectType'):
                                    tm1 = bytes(sblv3.text)
                                    st2 = self.DicTRealty.get(int(tm1[8]))
                                    if logst is not None:
                                        self.LOCK.acquire()
                                        self.master.txt1.insert(END, logst+st2+' '+st1+'\n')
                                        self.LOCK.release()
                                elif sblv3.tag.endswith('AssignationBuilding'):
                                    tm1 = bytes(sblv3.text)
                                    st3 = self.DicABuild.get(int(tm1[5]))
                                elif sblv3.tag.endswith('AssignationName'):
                                    st3 = sblv3.text
                                    if st3 is not None:
                                        st3 = st3.encode('utf-8')
                                    else:
                                        st3 = '-'
                                elif sblv3.tag.endswith('Area'): # Для здания
                                    st4 = self.DicPName.get(5)
                                    st5 = str(sblv3.text)
                                elif sblv3.tag.endswith('KeyParameters'): # Для сооружения и ОНС
                                    for sblv4 in sblv3:
                                        if sblv4.tag.endswith('KeyParameter'):
                                            st4 = self.DicPName.get(int(sblv4.get('Type')))
                                            st5 = sblv4.get('Value')
                                elif sblv3.tag.endswith('Address'):
                                    st6 = self.extract_address(sblv3)
                                elif sblv3.tag.endswith('EntitySpatial'):
                                    MIDStr = '"' + st1 + '","' + st2 + '","' + st3 + '","' + st4 + '","' + st5 + '","' + st6 + '"\n'
                                    MIDStr = MIDStr.decode('utf-8')
                                    MIDStr = MIDStr.encode('cp1251')
                                    for i in range(0,self.process_espatial(sblv3, 2)):
                                        self.MIDRealty.append(MIDStr)
            if logst is not None:
                self.correct_mif_bounds()
            return 0
        except:
            return 1

    def kvzu_v6(self,node):
        try:
            for sblv1 in node:
                if sblv1.tag.endswith('Parcels'):
                    for sblv2 in sblv1:
                        if sblv2.tag.endswith('Parcel'):
                            self.one_zu(sblv2,1)
            return 0
        except:
            return 1

    def kpzu_v5(self,node):
        try:
            for sblv1 in node:
                if sblv1.tag.endswith('Parcel'):
                    self.one_zu(sblv1,2)
            return 0
        except:
            return 1

    def one_zu(self,node,mode):
        #=======================================================================
        #  node - элемент XML с тэгом Parcel
        #  mode - вид обрабатываемого документа:
        #       1 - КВЗУ версии 6
        #       2 - КПЗУ версии 5
        #       3 - КПТ версии 9
        #=======================================================================
        CNP = node.get('CadastralNumber')
        self.LOCK.acquire()
        if mode == 1:
            self.master.txt1.insert(END, 'КВЗУ версии 6. Земельный участок '+CNP+'\n')
        elif mode == 2:
            self.master.txt1.insert(END, 'КПЗУ версии 5. Земельный участок '+CNP+'\n')
        self.LOCK.release()
        if mode != 3:
            self.named_parcel_files(CNP.replace(':', '_'))
        PCNP = '-'
        NmP = '-'
        StP = '-'
        ArP = 0
        CtP = '-'
        UtP = '-'
        AdP = '-'
        tm1 = node.get('State')
        StP = self.DicState.get(tm1)
        for sblv3 in node:
            if sblv3.tag.endswith('CadastralBlock'):
                CNCB = sblv3.text
            elif sblv3.tag.endswith('Name'):
                NmP = self.DicType.get(sblv3.text)
            elif sblv3.tag.endswith('Area'):
                for sblv4 in sblv3:
                    if sblv4.tag.endswith('Area'):
                        ArP = sblv4.text
            elif sblv3.tag.endswith('Location'):
                for sblv4 in sblv3:
                    if sblv4.tag.endswith('Address'):
                        AdP = self.extract_address(sblv4)
            elif sblv3.tag.endswith('Category'):
                tm2 = bytes(sblv3.text)
                CtP = self.DicCat.get(int(tm2[5]))
            elif sblv3.tag.endswith('Utilization'):
                UtP = sblv3.get('ByDoc')
            elif sblv3.tag.endswith('ParentCadastralNumbers'):
                for sblv4 in sblv3:
                    if sblv4.tag.endswith('CadastralNumber'):
                        PCNP = sblv4.text
            #=======================
            #   Многоконтурные
            #=======================
            elif sblv3.tag.endswith('Contours'):
                CtCnt = 0
                for sblv4 in sblv3:
                    if sblv4.tag.endswith('Contour'):
                        CtCnt+=1
                        A = (CNP+'('+str(CtCnt)+')',NmP,StP,str(ArP),CtP,UtP,AdP)
                        self.add_mid_str(A)
                        del A
                        for sblv5 in sblv4:
                            if sblv5.tag.endswith('EntitySpatial'):
                                if self.colormode == 0:
                                    self.process_espatial(sblv5, 1)
                                elif self.colormode == 1:
                                    self.process_espatial(sblv5, 1, int(tm2[5]))
                                elif self.colormode == 2:
                                    self.process_espatial(sblv5, 1, tm1)
            #===================================
            #   Одноконтурные
            #===================================
            elif sblv3.tag.endswith('EntitySpatial'):
                if PCNP != '-':
                    CNP = PCNP + '(' + CNP + ')'
                A = (CNP,NmP,StP,str(ArP),CtP,UtP,AdP)
                self.add_mid_str(A)
                del A
                if self.colormode == 0:
                    self.process_espatial(sblv3, 1)
                elif self.colormode == 1:
                    self.process_espatial(sblv3, 1, int(tm2[5]))
                elif self.colormode == 2:
                    self.process_espatial(sblv3, 1, tm1)
            #===================================
            #   Части участков
            #===================================
            elif sblv3.tag.endswith('SubParcels'):
                for sblv4 in sblv3:
                    if sblv4.tag.endswith('SubParcel'):
                        NumSP = sblv4.get('NumberRecord')
                        StSP = self.DicState.get(sblv4.get('State'))
                        for sblv5 in sblv4:
                            if sblv5.tag.endswith('Area'):
                                for sblv6 in sblv5:
                                    if sblv6.tag.endswith('Area'):
                                        ArSP = sblv6.text
                            elif sblv5.tag.endswith('Encumbrance'):
                                for sblv6 in sblv5:
                                    if sblv6.tag.endswith('Type'):
                                        TySP = self.DicEncumb.get(sblv6.text)
                                        if TySP is None:
                                            TySP = 'неизвестный код обременения'
                            elif sblv5.tag.endswith('EntitySpatial'):
                                self.process_espatial(sblv5, 7)
                                MIDStr = '"'+CNP+'","'+NumSP+'","'+StSP+'",'+ArSP+',"'+TySP+'"\n'
                                MIDStr = MIDStr.decode('utf-8')
                                MIDStr = MIDStr.encode('cp1251')
                                self.MIDSubParcel.append(MIDStr)
        if mode != 3:
            self.correct_mif_bounds()
        return 0

#==============================================================================
#
#   Класс потока автообновления
#
#==============================================================================
class AutoUpdThread(Thread):

    def __init__(self, mstr, ver, nm, hd):
        self.master = mstr
        self.cur_ver = ver
        self.selfname = path.join(hd, nm)
        self.tmpname = path.join(hd, 'retrieved.dat')
        self.upd_url = "http://sourceforge.net/projects/xml2mif/files/current_ver.json"
        self.LOCK = RLock()
        Thread.__init__(self)

    def run(self):
        try:
            buf = urllib.urlopen(self.upd_url)
            if buf != None:
                lst = json.loads(buf.read())
                if float(lst['ver']) > self.cur_ver:
                    urllib.urlretrieve(lst['pyw'], self.tmpname)
                    if path.exists(self.tmpname) and (hashlib.md5(open(self.tmpname, 'rb').read()).hexdigest() == lst['md5']):
                        move(self.tmpname, self.selfname)
                        urllib.urlretrieve(lst['txt'], self.tmpname)
                        if path.exists(self.tmpname):
                            tmp = codecs.open(self.tmpname, 'rb', encoding='utf-8').readlines()
                            self.LOCK.acquire()
                            for st in tmp:
                                self.master.txt1.insert(END, st.encode('utf-8'))
                            self.LOCK.release()
                            queue.put(lst['ver'])
                            remove(self.tmpname)
                    else:
                        pass # Checksum error
                else:
                    pass # Current version is up to date
        except:
            pass # Probably, Internet is unavailable

#==============================================================================
#
#   Класс главного окна
#
#==============================================================================
class main:

    def __init__(self, master, fname):
        self.master = master
        self.__version__ = 0.85
        self.__selfname__ = fname
        self.colorvar = StringVar()
        self.DicColorMethod = {
                                0:u'По умолчанию (одним цветом)',
                                1:u'В соответствии с категорией земель',
                                2:u'В соответствии со статусом участка'
                              }
        self.master.title('Импорт XML Росреестра')
        self.master.geometry('480x340')
        self.master.resizable(False, False)
        self.master.frame1=LabelFrame(root, height = 80, labelanchor='nw', text='Способ обработки')
        self.master.frame1.pack(side = 'top', fill = 'x', expand = 0, padx=2)
        self.master.frame3=LabelFrame(root, height = 55, labelanchor='nw', text='Метод окраски земельных участков')
        self.master.frame3.pack(side = 'top', fill = 'x', expand = 0, padx=2)
        self.master.frame2=Frame(root)
        self.master.frame2.pack(side = 'bottom', fill = 'both', expand = 1)
        self.rbvar=IntVar()
        self.rbvar.set(1)
        self.rbvar.trace_variable("w", self.callback_rbvar)
        if sys.platform.startswith('linux'):
            etrw = 24 # длина Entry
            btnw = 26 # длина кнопки Обработать / Закрыть
            ebtn_ipad = 0 # внутренняя добавка к ширине маленькой кнопки
        elif sys.platform.startswith('win'):
            etrw = 37 # в форточках все уже, надо добавлять
            btnw = 33
            ebtn_ipad = 4
        #================ Верхний фрейм =====================================================
        self.master.sf1=Frame(self.master.frame1)
        self.master.sf2=Frame(self.master.frame1)
        self.master.rb1=Radiobutton(self.master.sf1, text = 'Обработка одного XML файла', variable=self.rbvar, value=1)
        self.master.rb2=Radiobutton(self.master.sf2, text = 'Пакетная обработка XML', variable=self.rbvar, value=2)
        self.master.ebtn1=Button(self.master.sf1, width = 1, text = '...', command=self.ebtn1_press)
        self.master.ebtn2=Button(self.master.sf2, width = 1, text = '...', state=DISABLED, command=self.ebtn2_press)
        self.master.etr1=Entry(self.master.sf1, width = etrw)
        self.master.etr2=Entry(self.master.sf2, width = etrw, state=DISABLED)

        self.master.sf1.pack(pady = 1, fill = 'x')
        self.master.sf2.pack(pady = 1, fill = 'x')
        self.master.rb1.pack(side = 'left', padx = 2, fill = 'x')
        self.master.ebtn1.pack(side = 'right', padx = 2, ipadx = ebtn_ipad)
        self.master.etr1.pack(side = 'right', padx = 2)
        self.master.rb2.pack(side = 'left', padx = 2, fill = 'x')
        self.master.ebtn2.pack(side = 'right', padx = 2, ipadx = ebtn_ipad)
        self.master.etr2.pack(side = 'right', padx = 2)
        #=============== Нижний фрейм =======================================================
        self.master.sf3=Frame(self.master.frame2)
        self.master.lbl2=Label(self.master.sf3, text = 'Файлы MIF и MID будут созданы в папке, содержащей исходный XML-файл')
        self.master.btn1=Button(self.master.sf3, width = btnw, height = 1, text = 'Обработать', state=DISABLED, command=self.btn1_press)
        self.master.btn2=Button(self.master.sf3, width = btnw, height = 1, text = 'Закрыть', command=self.Quit)
        self.master.scrl=Scrollbar(self.master.frame2)
        self.master.txt1=Text(self.master.frame2, width = 5, yscrollcommand=(self.master.scrl, 'set'))
        self.master.scrl.configure(command = self.master.txt1.yview)
        self.master.sf3.pack(fill = 'x')
        self.master.lbl2.pack(anchor = 'w', side = 'top', padx = 2, pady = 2)
        self.master.btn1.pack(anchor = 'n', side = 'left', padx = 2, pady = 2, expand = 1)
        self.master.btn2.pack(anchor = 'n', side = 'right', padx = 2, pady = 2, expand = 1)
        self.master.scrl.pack(side = 'right', fill = 'y', pady = 1)
        self.master.txt1.pack(anchor = 's', side = 'bottom', fill = 'both', padx = 2)
        #=============== Средний фрейм =======================================================
        self.master.clrbtn = Menubutton(self.master.frame3, indicatoron = 1, anchor = 'w', textvariable = self.colorvar)
        self.clmenu = Menu(self.master.clrbtn, tearoff = 0, bg = 'white')
        self.master.clrbtn.configure(menu = self.clmenu)
        self.master.clrbtn.pack(side=LEFT, expand = 1, fill='x')
        for x in xrange(0,len(self.DicColorMethod)):
            self.clmenu.add_command(label = self.DicColorMethod[x], command = lambda x = x: self.set_active_clmth(x))
        self.colorvar.set(self.clmenu.entrycget(0, 'label'))
        AutoUpdThread(self.master, self.__version__, self.__selfname__, getcwd()).start()
        self.master.after(1000, self.task)
        self.master.mainloop()
        
    def set_active_clmth(self, idx):
        self.colorvar.set(self.clmenu.entrycget(idx, 'label'))
        
    def task(self):
        try:
            q = queue.get_nowait()  # получить значение из очереди
        except:  # если в очереди ничего нет, то возвращаем -1
            q = -1
        if q > 0:  
            showinfo(title = u'Обновление', message = u'Обновлено до версии '+str(q)+u'. Перезапустите программу.')
        self.master.after(1000, self.task)  # снова перезапускаем задачу после выполнения
        
    def callback_rbvar(self, *args):
        if self.rbvar.get()==1:
            self.master.etr1.config(state=NORMAL)
            self.master.etr2.config(state=DISABLED)
            self.master.ebtn1.config(state=NORMAL)
            self.master.ebtn2.config(state=DISABLED)
            if self.master.etr1.get() == '':
                self.master.btn1.config(state=DISABLED)
            else:
                self.master.btn1.config(state=NORMAL)
        elif self.rbvar.get()==2:
            self.master.etr1.config(state=DISABLED)
            self.master.etr2.config(state=NORMAL)
            self.master.ebtn1.config(state=DISABLED)
            self.master.ebtn2.config(state=NORMAL)
            if self.master.etr2.get() == '':
                self.master.btn1.config(state=DISABLED)
            else:
                self.master.btn1.config(state=NORMAL)

    def ebtn1_press(self):
        fn=Open(self.master, filetypes=[('XML Files', '.xml'),('ZIP Archives', '.zip')]).show()
        if fn == '':
           return
        else:
           self.master.etr1.delete(0,END)
           self.master.etr1.insert(0,path.normpath(fn))
           self.master.btn1.config(state=NORMAL)

    def ebtn2_press(self):
        dn=Directory(self.master).show()
        if dn == '':
           return
        else:
           self.master.etr2.delete(0,END)
           self.master.etr2.insert(0,path.normpath(dn))
           self.master.btn1.config(state=NORMAL)

    def btn1_press(self):
        if (self.rbvar.get() == 1) and (self.master.etr1.get() != ''):
           self.processfile(self.master.etr1.get(), self.DicColorMethod.values().index(self.colorvar.get()))
        elif (self.rbvar.get() == 2) and (self.master.etr2.get() != ''):
           self.processdir(self.master.etr2.get(), self.DicColorMethod.values().index(self.colorvar.get()))

    def Quit(self):
        self.master.destroy()

    def processfile(self,FName,clmode):
        FName=path.normpath(FName)
        if path.exists(FName):
            XMLThread(self.master, FName, clmode).start()

    def processdir(self,DName,clmode):
        dn=path.normpath(DName)
        if sys.platform.startswith('win'):
            dn = dn.encode('cp1251')
        XMLNames = []
        ZipNames = []
        #self.master.txt1.delete('1.0',END)
        for d, dirs, files in walk(dn):
            for f in files:
                if f.endswith('.xml'):
                    XMLNames.append(path.join(d,f))
                elif f.endswith('.zip'):
                    ZipNames.append(path.join(d,f))
        #===========================================================================
        # Из XMLNames убрать все файлы, которые найдутся внутри архивов 
        # для исключения повторной обработки
        #===========================================================================
        for ZipName in ZipNames:
            anm = path.split(ZipName)
            zin = ZipFile(ZipName, 'r')
            FNames = zin.namelist()
            FNames = filter(lambda x: x.endswith('.xml'), FNames)
            # Если в архиве есть файлы XML
            if len(FNames) > 0:
                for FName in FNames:
                    for XMLName in XMLNames:
                        xnm = path.split(XMLName)
                        if (anm[0] == xnm[0]) and (FName == xnm[1]):
                            XMLNames[XMLNames.index(XMLName)] = XMLName + '_'
            zin.close()
        for FName in ZipNames:
            fn = FName
            if sys.platform.startswith('win'):
                fn = fn.decode('cp1251')
            self.processfile(fn, clmode)
        for FName in XMLNames:
            fn = FName
            if sys.platform.startswith('win'):
                fn = fn.decode('cp1251')
            self.processfile(fn, clmode)
        
root=Tk()
queue = Queue()
main(root, sys.argv[0])
