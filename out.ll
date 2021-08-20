; ModuleID = 'pcfprog'


 


declare external ccc  i64* @pcf_mkclosure(i64* (i64*, i64*)*, i64, ...)    


declare external ccc  i64 @pcf_print(i64)    


define external ccc  i64* @__2(i64*  %__clo4, i64*  %__x3)    {
__2b:
  %__r_1 = inttoptr i64 1 to i64* 
  %__r_2 = ptrtoint i64* %__x3 to i64 
  %__r_3 = ptrtoint i64* %__r_1 to i64 
  %__r_4 = add   i64 %__r_2, %__r_3 
  %__c_0 = inttoptr i64 %__r_4 to i64* 
  %__r_5 = inttoptr i64 0 to i64* 
  %__r_6 = ptrtoint i64* %__c_0 to i64 
  %__r_7 = ptrtoint i64* %__r_5 to i64 
  %__r_8 = add   i64 %__r_6, %__r_7 
  %__2_reg = inttoptr i64 %__r_8 to i64* 
  ret i64* %__2_reg 
}


@y = internal   global i64* zeroinitializer


define external ccc  i64* @__7(i64*  %__clo9, i64*  %__x8)    {
__7b:
  %__r_1 = ptrtoint i64* %__x8 to i64 
  %__r_2 =  call ccc  i64  @pcf_print(i64  %__r_1)  
  %__c_1 = inttoptr i64 %__r_2 to i64* 
  %__r_3 = inttoptr i64 0 to i64* 
  %__r_4 = ptrtoint i64* %__c_1 to i64 
  %__r_5 = ptrtoint i64* %__r_3 to i64 
  %__r_6 = add   i64 %__r_4, %__r_5 
  %__7_reg = inttoptr i64 %__r_6 to i64* 
  ret i64* %__7_reg 
}


@_ = internal   global i64* zeroinitializer


define external ccc  i64* @pcfmain()    {
entry:
  %__c_2 =  call ccc  i64* (i64* (i64*, i64*)*, i64, ...) @pcf_mkclosure(i64* (i64*, i64*)*  @__2, i64  0)  
  %__r_2 = bitcast i64* %__c_2 to i64** 
  %addr1 = getelementptr  i64*, i64** %__r_2, i64 0 
  %__c_3 = load  i64*, i64** %addr1 
  %__c_4 =  call ccc  i64* (i64* (i64*, i64*)*, i64, ...) @pcf_mkclosure(i64* (i64*, i64*)*  @__2, i64  0)  
  %fun3 = bitcast i64* %__c_3 to i64* (i64*, i64*)* 
  %__r_4 = inttoptr i64 3 to i64* 
  %__c_5 =  call ccc  i64*  %fun3(i64*  %__c_4, i64*  %__r_4)  
  %__r_5 = inttoptr i64 0 to i64* 
  %__r_6 = ptrtoint i64* %__c_5 to i64 
  %__r_7 = ptrtoint i64* %__r_5 to i64 
  %__r_8 = add   i64 %__r_6, %__r_7 
  %__x1 = inttoptr i64 %__r_8 to i64* 
  %__r_9 = inttoptr i64 3 to i64* 
  %__r_10 = ptrtoint i64* %__x1 to i64 
  %__r_11 = ptrtoint i64* %__r_9 to i64 
  %__r_12 = add   i64 %__r_10, %__r_11 
  %__c_6 = inttoptr i64 %__r_12 to i64* 
  %__r_13 = inttoptr i64 0 to i64* 
  %__r_14 = ptrtoint i64* %__c_6 to i64 
  %__r_15 = ptrtoint i64* %__r_13 to i64 
  %__r_16 = add   i64 %__r_14, %__r_15 
  %__c_7 = inttoptr i64 %__r_16 to i64* 
  %__r_17 = inttoptr i64 0 to i64* 
  %__r_18 = ptrtoint i64* %__c_7 to i64 
  %__r_19 = ptrtoint i64* %__r_17 to i64 
  %__r_20 = add   i64 %__r_18, %__r_19 
  %___lv00 = inttoptr i64 %__r_20 to i64* 
  %__r_22 = load  i64*, i64** @suma 
  %__r_23 = bitcast i64* %__r_22 to i64** 
  %addr21 = getelementptr  i64*, i64** %__r_23, i64 0 
  %__c_8 = load  i64*, i64** %addr21 
  %fun24 = bitcast i64* %__c_8 to i64* (i64*, i64*)* 
  %__r_25 = load  i64*, i64** @suma 
  %__r_26 = inttoptr i64 1 to i64* 
  %__c_9 =  call ccc  i64*  %fun24(i64*  %__r_25, i64*  %__r_26)  
  %__r_28 = bitcast i64* %__c_9 to i64** 
  %addr27 = getelementptr  i64*, i64** %__r_28, i64 0 
  %__c_10 = load  i64*, i64** %addr27 
  %__r_30 = load  i64*, i64** @suma 
  %__r_31 = bitcast i64* %__r_30 to i64** 
  %addr29 = getelementptr  i64*, i64** %__r_31, i64 0 
  %__c_11 = load  i64*, i64** %addr29 
  %fun32 = bitcast i64* %__c_11 to i64* (i64*, i64*)* 
  %__r_33 = load  i64*, i64** @suma 
  %__r_34 = inttoptr i64 1 to i64* 
  %__c_12 =  call ccc  i64*  %fun32(i64*  %__r_33, i64*  %__r_34)  
  %fun35 = bitcast i64* %__c_10 to i64* (i64*, i64*)* 
  %__r_36 = inttoptr i64 2 to i64* 
  %__c_13 =  call ccc  i64*  %fun35(i64*  %__c_12, i64*  %__r_36)  
  %__r_38 = bitcast i64* %__c_13 to i64** 
  %addr37 = getelementptr  i64*, i64** %__r_38, i64 0 
  %__c_14 = load  i64*, i64** %addr37 
  %__r_40 = load  i64*, i64** @suma 
  %__r_41 = bitcast i64* %__r_40 to i64** 
  %addr39 = getelementptr  i64*, i64** %__r_41, i64 0 
  %__c_15 = load  i64*, i64** %addr39 
  %fun42 = bitcast i64* %__c_15 to i64* (i64*, i64*)* 
  %__r_43 = load  i64*, i64** @suma 
  %__r_44 = inttoptr i64 1 to i64* 
  %__c_16 =  call ccc  i64*  %fun42(i64*  %__r_43, i64*  %__r_44)  
  %__r_46 = bitcast i64* %__c_16 to i64** 
  %addr45 = getelementptr  i64*, i64** %__r_46, i64 0 
  %__c_17 = load  i64*, i64** %addr45 
  %__r_48 = load  i64*, i64** @suma 
  %__r_49 = bitcast i64* %__r_48 to i64** 
  %addr47 = getelementptr  i64*, i64** %__r_49, i64 0 
  %__c_18 = load  i64*, i64** %addr47 
  %fun50 = bitcast i64* %__c_18 to i64* (i64*, i64*)* 
  %__r_51 = load  i64*, i64** @suma 
  %__r_52 = inttoptr i64 1 to i64* 
  %__c_19 =  call ccc  i64*  %fun50(i64*  %__r_51, i64*  %__r_52)  
  %fun53 = bitcast i64* %__c_17 to i64* (i64*, i64*)* 
  %__r_54 = inttoptr i64 2 to i64* 
  %__c_20 =  call ccc  i64*  %fun53(i64*  %__c_19, i64*  %__r_54)  
  %fun55 = bitcast i64* %__c_14 to i64* (i64*, i64*)* 
  %__r_56 = inttoptr i64 3 to i64* 
  %__c_21 =  call ccc  i64*  %fun55(i64*  %__c_20, i64*  %__r_56)  
  %__r_57 = inttoptr i64 0 to i64* 
  %__r_58 = ptrtoint i64* %__c_21 to i64 
  %__r_59 = ptrtoint i64* %__r_57 to i64 
  %__r_60 = add   i64 %__r_58, %__r_59 
  %___lv15 = inttoptr i64 %__r_60 to i64* 
  %__r_61 = ptrtoint i64* %___lv00 to i64 
  %__r_62 = ptrtoint i64* %___lv15 to i64 
  %__r_63 = add   i64 %__r_61, %__r_62 
  %__c_22 = inttoptr i64 %__r_63 to i64* 
  %__r_64 = ptrtoint i64* %___lv00 to i64 
  %__r_65 = ptrtoint i64* %__c_22 to i64 
  %__r_66 = add   i64 %__r_64, %__r_65 
  %__c_23 = inttoptr i64 %__r_66 to i64* 
  %__r_67 = inttoptr i64 5 to i64* 
  %__r_68 = ptrtoint i64* %__r_67 to i64 
  %__r_69 = ptrtoint i64* %__c_23 to i64 
  %__r_70 = add   i64 %__r_68, %__r_69 
  %__c_24 = inttoptr i64 %__r_70 to i64* 
  %__r_71 = inttoptr i64 5 to i64* 
  %__r_72 = ptrtoint i64* %__r_71 to i64 
  %__r_73 = ptrtoint i64* %__c_24 to i64 
  %__r_74 = add   i64 %__r_72, %__r_73 
  %__c_25 = inttoptr i64 %__r_74 to i64* 
  %__r_75 = inttoptr i64 5 to i64* 
  %__r_76 = ptrtoint i64* %__r_75 to i64 
  %__r_77 = ptrtoint i64* %__c_25 to i64 
  %__r_78 = add   i64 %__r_76, %__r_77 
  %__c_26 = inttoptr i64 %__r_78 to i64* 
  %__r_79 = inttoptr i64 0 to i64* 
  %__r_80 = ptrtoint i64* %__c_26 to i64 
  %__r_81 = ptrtoint i64* %__r_79 to i64 
  %__r_82 = add   i64 %__r_80, %__r_81 
  %__c_27 = inttoptr i64 %__r_82 to i64* 
  %__r_83 = inttoptr i64 0 to i64* 
  %__r_84 = ptrtoint i64* %__c_27 to i64 
  %__r_85 = ptrtoint i64* %__r_83 to i64 
  %__r_86 = add   i64 %__r_84, %__r_85 
  %__c_28 = inttoptr i64 %__r_86 to i64* 
  %__r_87 = inttoptr i64 0 to i64* 
  %__r_88 = ptrtoint i64* %__c_28 to i64 
  %__r_89 = ptrtoint i64* %__r_87 to i64 
  %__r_90 = add   i64 %__r_88, %__r_89 
  %__r_91 = inttoptr i64 %__r_90 to i64* 
  store  i64* %__r_91, i64** @y 
  %__c_29 =  call ccc  i64* (i64* (i64*, i64*)*, i64, ...) @pcf_mkclosure(i64* (i64*, i64*)*  @__7, i64  0)  
  %__r_93 = bitcast i64* %__c_29 to i64** 
  %addr92 = getelementptr  i64*, i64** %__r_93, i64 0 
  %__c_30 = load  i64*, i64** %addr92 
  %__c_31 =  call ccc  i64* (i64* (i64*, i64*)*, i64, ...) @pcf_mkclosure(i64* (i64*, i64*)*  @__7, i64  0)  
  %fun94 = bitcast i64* %__c_30 to i64* (i64*, i64*)* 
  %__r_95 = load  i64*, i64** @y 
  %__c_32 =  call ccc  i64*  %fun94(i64*  %__c_31, i64*  %__r_95)  
  %__r_96 = inttoptr i64 0 to i64* 
  %__r_97 = ptrtoint i64* %__c_32 to i64 
  %__r_98 = ptrtoint i64* %__r_96 to i64 
  %__r_99 = add   i64 %__r_97, %__r_98 
  %__r_100 = inttoptr i64 %__r_99 to i64* 
  store  i64* %__r_100, i64** @_ 
  %__r_101 = inttoptr i64 0 to i64* 
  ret i64* %__r_101 
}