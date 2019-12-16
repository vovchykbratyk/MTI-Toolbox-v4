####################################################################
# STANAG 4607 Parser v4.0                                          #
#                                                                  #
# This tool is designed to allow ArcGIS Pro to parse STANAG 4607   #
# data into a series of feature classes. The tool will return      #
# feature classes containing GMTI hits, sensor location, and       #
# scan areas.                                                      #
#                                                                  #
# Point of Contact for this tool is Parker Hornstein               #
# Email: phornstein@esri.com Github: github.com/phornstein         #
#                                                                  #
# Version 4.0 11 December 2019                                     #
####################################################################

#import necessary packages
import codecs
import io
import numpy as np
import traceback
import base64
import sys
import os
import json
import datetime
from time import time
import arcpy
from arcpy.da import InsertCursor
from ast import literal_eval
from pathlib import Path

#########################################Declare Global Variables#########################################

segmentType = {'1':'Mission Segment',
            '2':'Dwell Segment',
            '3':'HRR Segment',
            '5':'Job Definition Segment',
            '6':'Free Text Segment',
            '7':'Low Reflectivity Index Segment',
            '8':'Group Segment',
            '9':'Attached Target Segment',
            '10':'Test and Status Segment',
            '11':'System-Specific Segment',
            '12':'Processing History Segment',
            '13':'Platform Location Segment',
            '101':'Job Request Segment',
            '102':'Job Acknowledgment Segment',
            '':''}


classification = {1:'TOP SECRET',
                2:'SECRET',
                3:'CONFIDENTIAL',
                4:'RESTRICTED',
                5:'UNCLASSIFIED',
                6:'OTHER',
                '':''}

caveat = {'0000':'NONE',
        '0001':'NOCONTRACT',
        '0002':'ORCON',
        '0004':'PROPIN',
        '0008':'WNINTEL',
        '0010':'NATIONAL ONLY',
        '0020':'LIMDIS',
        '0040':'FOUO',
        '0080':'EFTO',
        '0100':'LIM OFF USE (UNCLASS)',
        '0200':'NONCOMPARTMENT',
        '0400':'SPECIAL CONTROL',
        '0800':'SPECIAL INTEL',
        '1000':'CLASSIFICATION BASED ON EXISTENCE/AVAIL',
        '2000':'REL NATO',
        '4000':'REL 4-EYES',
        '8000':'REL 9-EYES',
        '':''}

exerciseInc = {'0':'Operation, Real Data',
            '1':'Operation, Simulated Data',
            '2':'Operation, Synthesized Data',
            '128':'Exercise, Real Data',
            '129':'Exercise, Simulated Data',
            '130':'Exercise, Synthesized Data',
            '':''}

sensor = {'0':'Unidentified',
        '1':'Other',
        '2':'HiSAR',
        '3':'ASTOR',
        '4':'Rotary Wing Radar',
        '5':'Global Hawk Sensor',
        '6':'HORIZON',
        '7':'APY-3',
        '8':'APY-6',
        '9':'APY-8 (Lynx I)',
        '10':'RADARSAT2',
        '11':'ASARS-2A',
        '12':'TESAR',
        '13':'MP-RTIP',
        '14':'APG-77',
        '15':'APG-79',
        '16':'APG-81',
        '17':'APY-6v1',
        '18':'DPY-1 (Lynx II)',
        '19':'SIDM',
        '20':'LIMIT',
        '21':'TCAR (AGC A321)',
        '22':'LSRS Sensor',
        '23':'UGS Single Sensor',
        '24':'UGS Cluster Sensor',
        '25':'IMASTER GMTI',
        '26':'AN/ZPY-1 (STARLite)',
        '27':'VADER',
        '255':'No Statement'}

platforms = {'0':'Unidentified',
        '1':'ACS',
        '2':'ARL-M',
        '3':'Sentinel (was ASTOR)',
        '4':'Rotary Wing Radar (was CRESO)',
        '5':'Global Hawk-Navy',
        '6':'HORIZON',
        '7':'E-8 (Joint STARS)',
        '8':'P-3C',
        '9':'Predator',
        '10':'RADARSAT2',
        '11':'U-2',
        '12':'E-10 (was MC2A)',
        '13':'UGS – Single',
        '14':'UGS – Cluster',
        '15':'Ground Based',
        '16':'UAV-Army',
        '17':'UAV-Marines',
        '18':'UAV-Navy',
        '19':'UAV-Air Force',
        '20':'Global Hawk- Air Force',
        '21':'Global Hawk-Australia',
        '22':'Global Hawk-Germany',
        '23':'Paul Revere',
        '24':'Mariner UAV',
        '25':'BAC-111',
        '26':'Coyote',
        '27':'King Air',
        '28':'LIMIT',
        '29':'NRL NP-3B',
        '30':'SOSTAR-X',
        '31':'WatchKeeper',
        '32':'Alliance Ground Surveillance (AGS) (A321)',
        '33':'Stryker',
        '34':'AGS (HALE UAV)',
        '35':'SIDM',
        '36':'Reaper',
        '37':'Warrior A',
        '38':'Warrior',
        '39':'Twin Otter',
        '255':'Other'}

terrain = {'0':'None Specified',
        '1':'DTED0 (Digital Terrain Elevation Data, Level 0)',
        '2':'DTED1 (Digital Terrain Elevation Data, Level 1)',
        '3':'DTED2 (Digital Terrain Elevation Data, Level 2)',
        '4':'DTED3 (Digital Terrain Elevation Data, Level 3)',
        '5':'DTED4 (Digital Terrain Elevation Data, Level 4)',
        '6':'DTED5 (Digital Terrain Elevation Data, Level 5)',
        '7':'SRTM1 (Shuttle Radar Topography Mission, Level 1)',
        '8':'SRTM2 (Shuttle Radar Topography Mission, Level 2)',
        '9':'DGM50 M745 (Digitales Gelandemodell 1:50 000)',
        '10':'DGM250 (Digitales Gelandemodell 1:250 000)',
        '11':'ITHD (Interferometric Terrain Data Height)',
        '12':'STHD (Stereometric Terrain Data Height)',
        '13':'SEDRIS (SEDRIS Reference Model, ISO/IEC 18026)'}

targetClassification ={0:'No Information, Live Target ',
                    1:'Tracked Vehicle, Live Target ',
                    2:'Wheeled Vehicle, Live Target ',
                    3:'Rotary Wing Aircraft, Live Target',
                    4:'Fixed Wing Aircraft, Live Target',
                    5:'Stationary Rotator, Live Target ',
                    6:'Maritime, Live Target  ',
                    7:'Beacon, Live Target  ',
                    8:'Amphibious, Live Target  ',
                    9:'Person, Live Target  ',
                    10:'Vehicle, Live Target  ',
                    11:'Animal, Live Target  ',
                    12:'Large Multiple-Return, Live Land Target',
                    13:'Large Multiple-Return, Live Maritime Target',
                    126:'Other, Live Target  ',
                    127:'Unknown, Live Target  ',
                    128:'No Information, Simulated Target ',
                    129:'Tracked Vehicle, Simulated Target ',
                    130:'Wheeled Vehicle, Simulated Target ',
                    131:'Rotary Wing Aircraft, Simulated Target',
                    132:'Fixed Wing Aircraft, Simulated Target',
                    133:'Stationary Rotator, Simulated Target ',
                    134:'Maritime, Simulated Target  ',
                    135:'Beacon, Simulated Target  ',
                    136:'Amphibious, Simulated Target  ',
                    137:'Person, Simulated Target  ',
                    138:'Vehicle, Simulated Target  ',
                    139:'Animal, Simulated Target  ',
                    140:'Large Multiple-Return, Simulated Land Target',
                    141:'Large Multiple-Return, Simulated Maritime Target',
                    143:'Tagging Device   ',
                    254:'Other, Simulated Target  ',
                    255:'Unknown, Simulated Target  '}

moverFields = ["reportIndex","geodeticHeight","tgtRadialVelocity","tgtWrapVelocity","tgtSNR","tgtClassification",
        "tgtClassificationUnc","tgtSlantRangeUnc","tgtCrossRangeUnc","tgtHeightUnc","tgtRadialVelocityUnc","truthTagApp","truthTagEntity",
        "tgtRadarCrossSect","detectTime","dwellIndex","revisitIndex","paltformType","sensorType","file","SHAPE@"]

moverFieldsTypes = ['LONG','LONG','LONG','LONG','LONG','TEXT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','TEXT','TEXT','LONG','DATE','LONG','LONG','TEXT','TEXT','TEXT']

sensorFields = ["revisitIndex","dwellIndex","lastDwellOfRevisit","targetReportCount","dwellTime","sensorAlt","sensorAltUncertainty",
        "sensorTrack","sensorSpeed","sensorVerticalVelocity","platformHeading","platformPitch","platformRoll","dwellCenterLat",
        "dwellCenterLon","dwellRangeHalfEx","dwellAngleHalfEx","sensorHeading","sensorPitch","sensorRoll","mdv","detectTime",
        "platformType","sensorType","file","SHAPE@"]

sensorFieldsTypes = ['LONG','LONG','LONG','LONG','LONG','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT',
        'FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','FLOAT','DATE','TEXT','TEXT','TEXT']

#########################################End Global Variables#############################################

#overwrite arcpy error handler for custom exceptions
class overwriteError(Exception):
    pass

#FieldMetaData class handles the structure file of GMTI data
class FieldMetaData:

    segment = ''
    name = ''
    numBytes = 0
    typeBytes = ''

    def __init__(self, seg, nm, bts, typ):
        self.segment = seg
        self.name = nm
        self.numBytes = bts
        self.typeBytes = typ

#readStruct is used to read the structure file into a list of fieldMetaData types
def readStruct():

    metaDataList = []

    base_path = Path(__file__).parent
    structFile = (base_path / "../MTI Toolbox v3/structure.txt").resolve()

    with open(structFile) as op:
        lines = op.readlines()
        lines = [line.strip('\n') for line in open(structFile)]

    seg = ''
    for line in lines: #for each line in the file
        if not(line.strip() == ''): #if the line is not empty
            if(line.startswith('#')):
                seg = line[1:]
            elif not(line.startswith('#')): #if the line does not start with #
                if not(line.startswith('##')): #if the line does not start with ##
                    s = line.split('\t') #split the line by tabs
                    fmd = FieldMetaData(seg, s[0],s[1],s[2])
                    metaDataList.append(fmd) #add the values to the metadata list as a FieldMetaData Object
    
    return metaDataList

#parse_ba and parse_sa are used for converting binary angles to floating points values
def parse_ba(coord):
    angle = 0.0
    const = 1.40625
    #angle = float(BAn-encoded-value)x1.40625x(1/2^n-8)
    #STANAG4607Ed3 pg B-24
    var = float(literal_eval(coord))*const
    if(len(coord) > 16):
        angle = var/(2**24)
    else:
        angle = var/(2**8)

    return angle

def parse_sa(coord):
    angle = 0.0
    const = 1.40625
    #angle = float(Sn-encoded-value)x1.40625#(1/2^n-7)
    #STANAG4607Ed3 pg B-25
    var = float(literal_eval(coord))*const
    if(len(coord) > 16):
        angle = var/(2**25)
    else:
        angle = var/(2**9)

    return angle

# the parseField function handles the conversion of each encoding type from binary
# to a plain text value that can be handled in the creation of feature classes
def parseField(i, instream):
    global metaDataList

    length = int(metaDataList[i].numBytes)
    typeParse = str(metaDataList[i].typeBytes)

    if(typeParse == 'A'):
        try:
            return instream.read(length).decode('utf-8')
        except:
            return ' '
    elif(typeParse == 'I'):
        return int.from_bytes(instream.read(length), byteorder='big')
    elif(typeParse == 'E'):
        return str(int.from_bytes(instream.read(length), byteorder='big',))
    elif(typeParse == 'F'):
        return instream.read(length).hex()
    elif(typeParse == 'S'):
        return int.from_bytes(instream.read(length), byteorder='big',signed=True)
    elif(typeParse == 'B'):
        wholeNum = str(int.from_bytes(instream.read(1), byteorder='big'))
        fraction = str(int.from_bytes(instream.read(length-1), byteorder='big'))
        bValue =  wholeNum + '.' + fraction
        return float(bValue)
    elif(typeParse == 'BA'):
        angle = bin(int.from_bytes(instream.read(length), byteorder='big', signed=False))
        return parse_ba(angle)
    elif(typeParse == 'SA'):
        angle = bin(int.from_bytes(instream.read(length), byteorder='big', signed=True))
        return parse_sa(angle)
    elif(typeParse == 'H'):
        return str(instream.read(length))

#The packetHeader is the first component sent with each mission and is responsible
#for the providing the base for the information to follow
def parsePacketHeader(instream):
    global metaDataList

    tl = 0
    header = {}
    i=0
    while True:
        fieldName = str(metaDataList[i].name)
        segment = str(metaDataList[i].segment)

        if segment == 'packetHeader':
            header.update({fieldName:parseField(i,instream)})
            tl += int(metaDataList[i].numBytes)
            i += 1
        else:
            return header, tl

#The segmentHeader returns the type and length of the next segment to be sent
def parseSegmentHeader(instream):
    global metaDataList
    tl = 0
    i = 10
    header = {}
    while True:
        fieldName = str(metaDataList[i].name)
        segment = str(metaDataList[i].segment)

        if segment == 'segmentHeader':
            header.update({fieldName:parseField(i,instream)})
            tl += int(metaDataList[i].numBytes)
            i += 1
        else:
            return header, tl

#the mission segment contains the date of mission, a key parameter for calculation
#of detectTime in each subsequent feature
def parseMissionSegment(instream):
    global metaDataList
    tl = 0
    i = 15
    missionSegment = {}
    while True:
        fieldName = str(metaDataList[i].name)
        segment = str(metaDataList[i].segment)

        if segment == 'missionSegment':
            missionSegment.update({fieldName:parseField(i,instream)})
            tl += int(metaDataList[i].numBytes)
            i += 1
        else:
            return missionSegment, tl

#the job definition carries import information such as sensor type 
def parseJobDefinition(instream):
    global metaDataList

    tl=0
    i = 53
    jobDefinition = {}
    while True:
        fieldName = str(metaDataList[i].name)
        segment = str(metaDataList[i].segment)
        if segment == 'jobDefinition':
            jobDefinition.update({fieldName:str(parseField(i,instream))})
            tl += int(metaDataList[i].numBytes)
            i += 1
        else:
            return jobDefinition, tl

#the dwellSegment contains the primary spatial data to be considered including:
#sensor location and the location of each detection
def parseDwellSegment(instream):
    global metaDataList

    existMask = str(bin(int.from_bytes(instream.read(8), byteorder='big')).lstrip('0b'))
    tl = 8
    i = 23
    j = 0
    dwellSegment = {}

    while True:
        segmentName = metaDataList[i].segment
        fieldName = metaDataList[i].name
        if(segmentName == 'segmentDwell'):
            if(existMask[j] == '1'):
                dwellSegment.update({fieldName:parseField(i,instream)})
                tl += int(metaDataList[i].numBytes)
                i += 1
                j += 1
            elif(existMask[j] == '0'):
                dwellSegment.update({fieldName:None})
                i += 1
                j += 1
        else:
            dwellSegment['sensorAlt'] = dwellSegment['sensorAlt']/100
            return dwellSegment, tl, existMask

#parseTargetReport handles the parsing of the targetReport section of the dwellSegement
def parseTargetReport(instream, mask):
    global metaDataList

    existMask = mask
    tl = 0
    i = 81
    j = 30
    targetReport = {}
    tgtCls = None

    while True:
        segmentName = metaDataList[i].segment
        fieldName = metaDataList[i].name
        if(segmentName == 'targetReport'):
            if(existMask[j] == '1'):
                targetReport.update({fieldName:parseField(i,instream)})
                tl += int(metaDataList[i].numBytes)
                i += 1
                j += 1
            elif(existMask[j] == '0'):
                targetReport.update({fieldName:None})
                i += 1
                j += 1
        else:
            tgtCls = targetReport['tgtClassification']
            try:
                targetReport['tgtClassification'] = targetClassification[int(tgtCls)]
            except:
                targetReport['tgtClassification'] = str(tgtCls)
            return targetReport, tl

#platform location segment sends sensor tracks when no dwells are recorded
def parsePlatformLocation(instream):
    global metaDataList

    tl=0
    i=130
    platformLocation = {}
    while True:
        fieldName = str(metaDataList[i].name)
        segment = str(metaDataList[i].segment)
        if segment == 'platformLocation':
            platformLocation.update({fieldName:parseField(i,instream)})
            tl += int(metaDataList[i].numBytes)
            i += 1
        else:
            return platformLocation, tl   

#The parseDwellTime function handles the conversion of time being sent from
#milliseconds to a standard time after midnight on the day of the mission
def parseDwellTime(dwellTime):
    global day, month, year

    dt_time = datetime.datetime.strptime('{}/{}/{}'.format(year,month,day),'%Y/%m/%d')
    dt_time = dt_time.timestamp() * 1000
    dt_time = dt_time + dwellTime
    dt_time = datetime.datetime.fromtimestamp(dt_time/1000)
    fullTime = dt_time.strftime('%Y-%m-%d %H:%M:%S.%f')
    fullTime = datetime.datetime.strptime(fullTime, '%Y-%m-%d %H:%M:%S.%f')

    return fullTime

#dwellPolygon converts data sent in the dwellSegment to scan area polygons
def dwellPolygon(centerPt,rangStr,angleStr,sensorPt):
    global sr

    rang = float(rangStr)*1000
    angle = float(angleStr)

    centerPoint = arcpy.PointGeometry(centerPt, sr)
    sensorPoint = arcpy.PointGeometry(sensorPt, sr)
    distAng = sensorPoint.angleAndDistanceTo(centerPoint, method='GREAT_ELLIPTIC')
    nearDist = distAng[1] - rang
    farDist = distAng[1] + rang

    ptA = sensorPoint.pointFromAngleAndDistance(distAng[0]-angle,nearDist, method='GREAT_ELLIPTIC')
    ptB = sensorPoint.pointFromAngleAndDistance(distAng[0]-angle,farDist, method='GREAT_ELLIPTIC')
    ptC = sensorPoint.pointFromAngleAndDistance(distAng[0]+angle,farDist, method='GREAT_ELLIPTIC')
    ptD = sensorPoint.pointFromAngleAndDistance(distAng[0]+angle,nearDist, method='GREAT_ELLIPTIC')

    return ptA.firstPoint, ptB.firstPoint, ptC.firstPoint, ptD.firstPoint

#utils for populating feature classes with data
def buildMoversFC(points_att):
    global sr, moverFields, moverFieldsTypes

    movers_fc = arcpy.CreateFeatureclass_management(r'memory','movers','POINT',None,None,'ENABLED',sr)
    for field in range(0, len(moverFieldsTypes)):
        arcpy.AddField_management(movers_fc, moverFields[field], moverFieldsTypes[field])

    movers_cursor = InsertCursor(movers_fc, moverFields)
    for i in range(len(points_att)):
        rptIdx,lat,lon,dlat,dlon,ghgt,RV,WV,SNR,CLS,CU,SRU,CRU,HU,RVU,TTA,TTE,RCS,DT,DI,RI,PT,ST,F = points_att[i].values()
        movers_cursor.insertRow([rptIdx,ghgt,RV,WV,SNR,CLS,CU,SRU,CRU,HU,RVU,TTA,TTE,RCS,DT,DI,RI,PT,ST,F,arcpy.Point(lon,lat,ghgt)])
    del movers_cursor

    return movers_fc

def buildSensorFC(sensor_att, platformLoc_att):
    global sr, sensorFields, sensorFieldsTypes

    sensor_fc = arcpy.CreateFeatureclass_management(r'memory','sensor','POINT',None,None,'ENABLED',sr)
    for field in range(0, len(sensorFieldsTypes)):
        arcpy.AddField_management(sensor_fc, sensorFields[field], sensorFieldsTypes[field])
    
    sensor_cursor = InsertCursor(sensor_fc, sensorFields)
    for i in range(len(sensor_att)):
        RI,DI,DR,TRC,DT,lat,lon,alt,LaS,LoS,sua,suc,SAU,ST,SS,SVV,stu,ssu,vvu,PH,PP,PR,DCLa,DCLo,DRH,DAH,SH,SP,SR,MDV,DCT,PT,SenT,F = sensor_att[i].values()
        try:
            sensor_cursor.insertRow([RI,DI,DR,TRC,DT,alt,SAU,ST,SS,SVV,PH,PP,PR,DCLa,DCLo,DRH,DAH,SH,SP,SR,MDV,DCT,PT,SenT,F,arcpy.Point(lon,lat,alt/100)])
        except:
            arcpy.AddMessage('{} \n {}'.format('Error inserting values:',sensor_att[i].values()))
    if not len(platformLoc_att) == 0:
        for j in range(len(platformLoc_att)):
            time,lat,lon,alt,track,speed,vertVel,dTime,fName = platformLoc_att[j].values()
            sensor_cursor.insertRow([None,None,None,None,time,alt,None,None,speed,vertVel,track,None,None,None,None,None,None,None,None,None,None,dTime,None,None,fName,arcpy.Point(lon,lat,alt/100)])
    del sensor_cursor

    return sensor_fc

def buildScanAreaFC(sensor_att, poly_arr):
    global sr, sensorFields, sensorFieldsTypes

    scans_fc = arcpy.CreateFeatureclass_management(r'memory','scans','POLYGON',None,None,None,sr)
    for field in range(0, len(sensorFieldsTypes)):
        arcpy.AddField_management(scans_fc, sensorFields[field], sensorFieldsTypes[field])

    polygon_cursor = InsertCursor(scans_fc, sensorFields)

    aa = 0
    for i in range(0, len(polygon_array), 4):
        points = arcpy.Array()
        points.add(polygon_array[i])
        points.add(polygon_array[i+1])
        points.add(polygon_array[i+2])
        points.add(polygon_array[i+3])

        RI,DI,DR,TRC,DT,lat,lon,alt,LaS,LoS,sua,suc,SAU,ST,SS,SVV,stu,ssu,vvu,PH,PP,PR,DCLa,DCLo,DRH,DAH,SH,SP,SR,MDV,DCT,PT,SenT,F = sensor_att[aa].values()
        polygon_cursor.insertRow([RI,DI,DR,TRC,DT,alt,SAU,ST,SS,SVV,PH,PP,PR,DCLa,DCLo,DRH,DAH,SH,SP,SR,MDV,DCT,PT,SenT,F,arcpy.Polygon(points, sr)])
        aa+=1

    del polygon_cursor

    return scans_fc

def parseFile(path):
    global metaDataList, sr, day, month, year, sensorType, platformType, platformsUsed, points_att_array, sensor_att_array, polygon_array, platformLoc_seg_array, highestClassification, caveats

    scans_fc = arcpy.CreateFeatureclass_management(r'memory','scans','POLYGON',None,None,None,sr)

    #open current file
    instream = open(path, 'rb')

    fileName = os.path.basename(path)

    out = []
    last_position = instream.tell()

    while instream.read(1) != b'':
        instream.seek(last_position)
        currentSegSize = 0
        currentPktLength = 0 #variable to count number of bytes in packet that have been read
        packetHeader, packetLength = parsePacketHeader(instream) #read packet header, return parsed header and number of bytes in the header
        if packetHeader['versionID'] in ['10','20','30']:
            currentPktLength += packetLength #add the bytes in the packet header to total count of bytes
            out.append(packetHeader) #add the header to output list

            if int(packetHeader['classification']) < highestClassification:
                highestClassification = int(packetHeader['classification'])
            if packetHeader['caveat'] not in caveats:
                caveats.append(packetHeader['caveat'])

            packetSize = packetHeader['packetSize'] #retrieve the total number of bytes in this packet
                
            while currentPktLength < int(packetSize): #while the current count of bytes is less than the total expected bytes
                #after identifying a packet header always expect a segment header
                segmentHeader, segmentLength = parseSegmentHeader(instream) #read segment header, return parsed header and number of bytes in the header
                out.append(segmentHeader) #add the header to output list

                segmentType = str(segmentHeader['segmentType']) #get type of segment to parse for as a string
                currentPktLength += segmentLength #add bytes from segment header to the total bytes expected for this segment
                currentSegSize += segmentLength

                if segmentType == '1':
                    missionSegment, msnSegLength = parseMissionSegment(instream)
                    out.append(missionSegment)
                    currentPktLength += msnSegLength
                    currentSegSize += msnSegLength
                    last_position = instream.tell()

                    day = missionSegment['day']
                    month = missionSegment['month']
                    year = missionSegment['year']

                    try:
                        platformType = platforms[missionSegment['platformType']]
                    except:
                        platformType = platforms['255']
                    if platformType not in platformsUsed:
                        platformsUsed.append(platformType)


                elif segmentType == '5':
                    jobDefinition, jobDefLength = parseJobDefinition(instream) #type 5 is a job definition, parse the definition
                    #arcpy.AddMessage(jobDefinition)
                    out.append(jobDefinition) #add job definition to output list
                    currentPktLength += jobDefLength #add bytes from the job definition to the total current bytes
                    currentSegSize += jobDefLength
                    last_position = instream.tell()

                    try:
                        sensorType = sensor[jobDefinition['sensorType']] #get sensor type attribute and convert to plain text
                    except:
                        sensorType = sensor['0']
                    
                    try:
                        tModel = terrain[jobDefinition['terrainElevationModel']]
                    except:
                        tModel = terrain['0']
                    if tModel not in terrainModel: #collect terrain models used in this collection for processing report
                        terrainModel.append(tModel)

                elif segmentType == '2':
                    dwellSegment, dwellSegLength, existMask = parseDwellSegment(instream)
                    out.append(dwellSegment)
                    currentPktLength += dwellSegLength
                    currentSegSize += dwellSegLength
                    last_position = instream.tell()

                    try:
                        fullTime = parseDwellTime(dwellSegment['dwellTime'])
                    except:
                        fullTime = None
                    
                    dwellSegment.update({'detectTime':fullTime})
                    dwellSegment.update({'platformType':platformType})
                    dwellSegment.update({'sensorType':sensorType})
                    dwellSegment.update({'file':fileName})
                    sensor_att_array.append(dwellSegment)

                    sensor_loc = arcpy.Point(dwellSegment['sensorLon'],dwellSegment['sensorLat'],int(dwellSegment['sensorAlt'])/100)
                    center_loc = arcpy.Point(dwellSegment['dwellCenterLon'],dwellSegment['dwellCenterLat'])
                    scanArea = dwellPolygon(center_loc,dwellSegment['dwellRangeHalfEx'],dwellSegment['dwellAngleHalfEx'],sensor_loc)

                    for pt in scanArea:
                        polygon_array.add(pt)

                    targetMask = existMask
                    targetRptCnt = int(dwellSegment['targetReportCount'])
                    if not targetRptCnt == 0:
                        for s in range(0, targetRptCnt):
                            targetReport, targetReportLength = parseTargetReport(instream, targetMask)

                            targetReport.update({'detectTime':fullTime})
                            targetReport.update({'dwellIndex':dwellSegment['dwellIndex']})
                            targetReport.update({'revisitIndex':dwellSegment['revisitIndex']})
                            targetReport.update({'platformType':platformType})
                            targetReport.update({'sensorType':sensorType})
                            targetReport.update({'file':fileName})
                            out.append(targetReport)
                            points_att_array.append(targetReport)

                            currentPktLength += targetReportLength
                            currentSegSize += targetReportLength
                            last_position = instream.tell()

                elif segmentType == '13':
                    platformLoc, platformLocLen = parsePlatformLocation(instream)
                    out.append(platformLoc)
                    currentPktLength += platformLocLen
                    currentSegSize += platformLocLen
                    last_position = instream.tell()

                    if not day == month == year:
                        fullTime = parseDwellTime(platformLoc['platformLocationTime'])
                    else:
                        fullTime = None
                    # fullTime = None

                    platformLoc.update({'detectTime':fullTime})
                    platformLoc.update({'file':fileName})

                    platformLoc_seg_array.append(platformLoc)

                else:
                    arcpy.AddMessage('{}: {}'.format('Unrecognized Segment', segmentType))
                    toRead = int(packetSize)-int(currentPktLength)
                    instream.read(toRead)
                    currentPktLength += toRead
                    last_position = instream.tell()
        else:
            instream.seek(last_position)
            instream.read(1)
            last_position = instream.tell()



    #return points_att_array, sensor_att_array, polygon_array

metaDataList = readStruct() #managing structure file of segments
sr = "4326" #declaring a global spatial reference as a default
day = '' #global variables for date
month = ''
year = ''
sensorType = '' #sensor type from collection
platformType = ''
platformsUsed = []
#######STANAG4607 ed3 pg A-46
radarMode = '' #To be added, radar mode is a coded value in Job Definition Segment, also contains platform type
terrainModel = [] #a list of all terrain models used in collection
polygon_array = arcpy.Array() #array for holding corner points of scan areas
points_att_array = [] #array for holding attributes related to movers
sensor_att_array = [] #array for holding attributes related to sensor
platformLoc_seg_array = []
highestClassification = 7
caveats = []

def main():
    global points_att_array, sensor_att_array, polygon_array, sr, highestClassification

    files = arcpy.GetParameter(0)

    fileCount = 0
    for f in files:
        fileCount += 1
        arcpy.SetProgressorLabel('{}{}{}{}'.format('Parsing File ',str(fileCount),' of ',str(len(files))))
        path = os.path.abspath(str(f))
        parseFile(path)


    featureClasses = []
    if not arcpy.GetParameterAsText(2) == '':
        output_movers_fc = buildMoversFC(points_att_array)
        if not arcpy.GetParameterAsText(1) == '':
            arcpy.SetProgressorLabel('{}'.format('Selecting detections in AOI...'))
            aoi_movers = arcpy.SelectLayerByLocation_management(output_movers_fc,'INTERSECT',arcpy.GetParameter(1))
            arcpy.SetProgressorLabel('{}'.format('Building movers feature class...'))
            arcpy.CopyFeatures_management(aoi_movers,arcpy.GetParameterAsText(2))
            featureClasses.append(arcpy.GetParameterAsText(2))            
        else:
            arcpy.SetProgressorLabel('{}'.format('Building movers feature class...'))
            arcpy.CopyFeatures_management(output_movers_fc,arcpy.GetParameterAsText(2))
            featureClasses.append(arcpy.GetParameterAsText(2))   

    if not arcpy.GetParameterAsText(3) == '':
        arcpy.SetProgressorLabel('{}'.format('Building sensor feature class...'))
        output_sensor_fc = buildSensorFC(sensor_att_array,platformLoc_seg_array)
        arcpy.CopyFeatures_management(output_sensor_fc,arcpy.GetParameterAsText(3))
        featureClasses.append(arcpy.GetParameterAsText(3))   

    if not arcpy.GetParameterAsText(4) == '':
        arcpy.SetProgressorLabel('{}'.format('Building scans feature class...'))
        output_scans_fc = buildScanAreaFC(sensor_att_array,polygon_array)
        arcpy.CopyFeatures_management(output_scans_fc,arcpy.GetParameterAsText(4))
        featureClasses.append(arcpy.GetParameterAsText(4))

    if not arcpy.GetParameterAsText(5) == '':
        arcpy.SetProgressorLabel('{}'.format('Projecting Data to Spatial Reference...'))
        for fc in featureClasses:
            out_fc = fc + '_unprojected'
            arcpy.Project_management(fc,out_fc,arcpy.GetParameter(5))   
            arcpy.CopyFeatures_management(out_fc,fc)
            arcpy.Delete_management(out_fc)

    terrainUsed = ''
    for value in terrainModel:
        terrainUsed = terrainUsed + '\n' + value
    
    allPlatforms = ''
    for value in platformsUsed:
        allPlatforms = allPlatforms +'\n' + value

    try:
        finalClassification = classification[highestClassification]
    except:
        finalClassification = ''
    for value in caveats:
        try:
            cav = caveat[value]
        except:
            cav = value

        finalClassification = finalClassification + '//' + cav

    report = '''Processing report:
    #############################################
    Highest Classification of Data: {}

    Number of files processed: {}

    Terrain model(s) used in collection: {}
    
    Platform(s) used in collection: {}
    
    #############################################
    '''.format(finalClassification,fileCount,terrainUsed, allPlatforms)

    arcpy.AddMessage(report)

if __name__ == '__main__':
    main()
