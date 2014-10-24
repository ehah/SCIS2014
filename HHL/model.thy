theory train
  imports HHL
begin

definition ts :: "exp" where
"ts == RVar ''ts''"
definition tv :: "exp" where
"tv == RVar ''tv''"
definition ta :: "exp" where
"ta == RVar ''ta''"
definition t :: "exp" where
"t == RVar ''t''"

consts
sb :: real
b :: real
A :: real

definition cs :: "exp" where
"cs == RVar ''cs''"
definition cv :: "exp" where
"cv == RVar ''cv''"
definition ct :: "exp" where
"ct == RVar ''ct''"
definition ca :: "exp" where
"ca == RVar ''ca''"
definition temp :: "exp" where
"temp == RVar ''temp''"

definition v11 :: "exp" where
"v11 == RVar ''v11''"
definition v12 :: "exp" where
"v12 == RVar ''v12''"
definition v21 :: "exp" where
"v21 == RVar ''v21''"
definition v22 :: "exp" where
"v22 == RVar ''v22''"
definition e :: "exp" where
"e == RVar ''e''"
consts
period :: real

definition eoa :: "exp" where
"eoa == RVar ''eoa''"

consts
cha :: "cname"
chs :: "cname"
chv :: "cname"

axioms
assSb: "sb>0"
assMinA: "b>0"
assMaxA: "A>0"
assPeriod: "period>0"
assEOA: "|- e[>](Real 0)"

definition DSPV1 :: "fform" where
"DSPV1 == v12[*]v12 [+] (Real 2*b)[*]cs [<=] v22[*]v22 [+] (Real 2*b)[*]e"
definition DSPV2 :: "fform" where
"DSPV2 == v11[*]v11 [+] (Real 2*b)[*]cs [<=] v12[*]v12 [+] (Real 2*b)[*]e"
definition DSPV :: "fform" where
"DSPV == tv[*]tv [+] (Real 2*b)[*]ts [<=] (Real 2*b)[*]e"

definition M1 :: "mid" where
"M1 == (v22[=](Real 0)[&]eoa[=]e, l[=](Real 0))"
definition M2 :: "mid" where
"M2 == (v22[=](Real 0)[&]eoa[=]e, l[=](Real 0))"
definition M3 :: "mid" where
"M3 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ca[<](Real 0)), l[=](Real 0))"
definition M4 :: "mid" where
"M4 == (v22[=](Real 0)[&]eoa[=]e, l[=](Real 0))"
definition M5 :: "mid" where
"M5 == (DSPV, l[=](Real 0))"
definition M6 :: "mid" where
"M6 == (DSPV, l[=](Real 0))"
definition M7 :: "mid" where
"M7 == (DSPV[&]v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b)), l[=](Real 0))"
definition M8 :: "mid" where
"M8 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ca[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ca[=](Real -b)), l[=](Real 0))"
definition M9 :: "mid" where
"M9 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b)), l[=](Real 0))"
definition M10 :: "mid" where
"M10 == (WTrue, l[=](Real 0))"
definition M11 :: "mid" where
"M11 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b)), l[=](Real 0))"
definition M12 :: "mid" where
"M12 == (DSPV, l[=](Real 0))"
definition M13 :: "mid" where
"M13 == (DSPV, l[=](Real 0))"
definition M14 :: "mid" where
"M14 == (WTrue, l[=](Real 0))"
definition M15 :: "mid" where
"M15 == (DSPV, l[=](Real 0))"
definition M16 :: "mid" where
"M16 == (DSPV, l[=](Real 0))"
definition M17 :: "mid" where
"M17 == (WTrue, l[=](Real 0))"
definition M18 :: "mid" where
"M18 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b)), l[=](Real period))"
definition M19 :: "mid" where
"M19 == (v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b)), l[=](Real period))"

definition control :: "proc" where
"control == (chs??cs;M1;chv??cv;M2;((IF ((cv[>=]v12[|][~] DSPV2)) ca:=(Real -sb));M3;(IF (cv[>=]v11[|][~] DSPV1) ca:=(Real -b)));M8;cha!!ca);M4;<WTrue && WTrue>:(l[=] Real period)"

definition inv :: "fform" where
"inv == DSPV"

definition train :: "proc" where
"train == (chs!!ts;M5;chv!!tv;M6;cha??ta);M7;<inv && WTrue>:(l[=]Real period)"

definition System :: "proc" where
"System == control* || train*"

lemma System_Proof : 
"{v21[=](Real 0)[&]v22[=](Real 0)[&]eoa[=]e,
  ts[=](Real 0)[&]tv[=](Real 0)[&]t[=](Real 0)} 
 System
 {WTrue,WTrue; WTrue,
  high(((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0))
  [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))
  [&] (ts[<=]eoa[&](ts[=]eoa [-->] tv[=](Real 0))))}"
apply(simp add: System_def)
apply(cut_tac px ="v22[=](Real 0)[&]eoa[=]e" and py="DSPV" and qx="v22[=](Real 0)[&]eoa[=]e" and qy="DSPV" and Hx="WTrue" and Hy="high(((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))[&](ts[<=]eoa[&](ts[=]eoa [-->] tv[=](Real 0))))" in ConsequenceP,auto)
defer
apply (rule conjR)
apply(rule Trans)
apply(simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule conjR)
apply(simp add: DSPV_def)
apply(rule impR)
apply(cut_tac P="(Real b)[>](Real 0) [&] e[>](Real 0)" in cut, auto)
apply(rule thinR, rule thinL, rule conjR, rule Trans, simp, rule assMinA, rule assEOA)
apply(rule Trans2, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(metis mult_pos_pos)
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule Repetition)
defer
apply(rule Trans, simp)
apply(rule impR, rule DCL3, rule basic)
apply(simp add: control_def train_def M4_def M7_def)
apply(cut_tac m="0" and Hx="WTrue" and Hy="WTrue" and Mx="WTrue" and My="high(((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))[&](ts[<=]eoa[&](ts[=]eoa [-->] tv[=](Real 0))))" in Parallel3,auto)
defer defer
apply(rule impR, rule conjL, rule basic)+
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule Trans1, simp)
apply(rule conjL, rule basic)
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule LL3a, rule basic)
apply(rule conjL, rule basic)
prefer 2
apply(rule Parallel2)
apply(cut_tac px="WTrue [&] v22[=](Real 0)[&]eoa[=]e" and qx="v22[=](Real 0)[&]eoa[=]e" and Hx="WTrue" in ConsequenceS, auto)
prefer 2
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule Continue)
apply(rule conjR)
apply(rule Trans, simp add: v22_def)
apply(rule conjR)
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule impR, rule conjL, rule disjL)
apply(cut_tac P="(Real period) [>] (Real 0)" in cut, auto)
apply(rule thinL)+
apply(rule thinR, rule Trans, simp, rule assPeriod)
apply(cut_tac P="WFalse" in cut, auto)
apply(rule thinR, rule Trans3, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def DSPV1_def DSPV2_def ltrans)
apply (metis less_numeral_extra(3))
apply(rule FalseL)
apply(cut_tac P="l [=] Real period" in thinL, auto)
apply(rule Trans1, simp)
apply(cut_tac px="DSPV [&] DSPV [&] v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))" and qx="DSPV" and Hx="high(((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ta[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))[&](ts[<=]eoa[&](ts[=]eoa [-->] tv[=](Real 0))))" in ConsequenceS, auto)
prefer 2
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule Continue)
apply(rule conjR)
apply(rule Trans, simp add: train.inv_def)
apply(rule conjR)
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def)
apply(rule impR, rule conjL, rule disjL)
apply(cut_tac P="(Real period) [>] (Real 0)" in cut, auto)
apply(rule thinL)+
apply(rule thinR, rule Trans, simp, rule assPeriod)
apply(cut_tac P="WFalse" in cut, auto)
apply(rule thinR, rule Trans3, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def DSPV1_def DSPV2_def ltrans)
apply (metis less_numeral_extra(3))
apply(rule FalseL)
apply(cut_tac P="l [=] Real period" in thinL, auto)
apply(rule DC18)
apply(rule conjL, rule thinL)
apply(rule conjL)+
apply(rule conjR, rule basic)+
apply(cut_tac P="((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ta[=](Real -b))" in thinL, auto)
apply(cut_tac P="((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->]ta[<](Real 0))" in thinL, auto)
apply(cut_tac P="WTrue" in thinL, auto)
apply(rule Trans3, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def DSPV1_def DSPV2_def ltrans)
apply (smt assMinA real_minus_mult_self_le real_mult_le_cancel_iff2 real_two_squares_add_zero_iff)
apply(simp add: M1_def M5_def)
apply(cut_tac m="0" and Hx="WTrue" and Hy="WTrue" and Mx="l[=](Real 0)" and My="l[=](Real 0)" in Parallel3,auto)
defer defer
apply(rule impR, rule conjL, rule basic)+
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule LL3a, rule Trans1, simp add: ltrans)
apply(rule conjL, rule basic)
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule LL3a, rule Trans1, simp add: ltrans)
apply(rule conjL, rule basic)
apply(rule Structure)
apply(cut_tac px ="DSPV" and py="v22[=](Real 0)[&]eoa[=]e" and qx="DSPV" and qy="v22[=](Real 0)[&]eoa[=]e" and Hx="l [=] Real 0" and Hy="l [=] Real 0" in ConsequenceP,auto)
prefer 2
apply(rule conjR, rule impR, rule basic)+
apply(rule conjR, rule impR, rule Trans1, simp add: ltrans)
apply(rule impR, rule Trans1, simp add: ltrans)
apply(rule CommunicationSim)
apply(simp add: cs_def ts_def v22_def eoa_def e_def)
apply(rule Trans, simp add: v22_def eoa_def e_def cs_def ts_def)
apply(simp add: M2_def M6_def)
apply(cut_tac m="0" and Hx="WTrue" and Hy="WTrue" and Mx="l[=](Real 0)" and My="l[=](Real 0)" in Parallel3,auto)
defer defer
apply(rule impR, rule conjL, rule basic)+
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule LL3a, rule Trans1, simp add: ltrans)
apply(rule conjL, rule basic)
apply(rule impR, cut_tac R="l[=](Real 0)" in CML,auto)
apply(rule LL3a, rule Trans1, simp add: ltrans)
apply(rule conjL, rule basic)
apply(rule Structure)
apply(cut_tac px ="DSPV" and py="v22[=](Real 0)[&]eoa[=]e" and qx="DSPV" and qy="v22[=](Real 0)[&]eoa[=]e" and Hx="l [=] Real 0" and Hy="l [=] Real 0" in ConsequenceP,auto)
prefer 2
apply(rule conjR, rule impR, rule basic)+
apply(rule conjR, rule impR, rule Trans1, simp add: ltrans)
apply(rule impR, rule Trans1, simp add: ltrans)
apply(rule CommunicationSim)
apply(simp add: cs_def ts_def v22_def eoa_def e_def)
apply(rule Trans, simp add: v22_def eoa_def e_def cv_def tv_def)
apply(rule Structure)
apply(simp add: M8_def)
apply(cut_tac Hy="l[=](Real 0)" and My="l[=](Real 0)" in Parallel4, auto)
prefer 3 prefer 4
apply(rule impR, rule LL4, rule conjL, rule basic)
apply(rule impR, rule conjL, rule basic)
apply(cut_tac px="v22[=](Real 0)[&]eoa[=]e" and qx="v22[=](Real 0)[&]eoa[=]e[&]((cv[>=]v12[|][~] DSPV2)[&](t[>](temp[+](Real period))) [-->] ca[<](Real 0)) [&] ((cv[>=]v11[|][~] DSPV1)[&](t[>](temp[+](Real period))) [-->]ca[=](Real -b))" and Hx="l [=] Real 0 [^] l [=] Real 0" in ConsequenceS, auto)
prefer 2
apply(rule conjR, rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule conjR, rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule impR, rule conjR, rule LL4, rule basic, rule LL4, rule basic)
apply(simp add: M3_def)
apply(rule Sequence)
apply(cut_tac b="(cv[>=]v12[|][~] DSPV2)" in Case, auto)
apply(rule ConditionT)
apply(rule impR, rule conjL, rule basic)
apply(rule Assign)
apply(simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule conjR)
apply(cut_tac P="(Real sb)[>](Real 0)" in cut, auto)
apply(rule thinR, rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule assSb)
apply(rule Trans1, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def, rule impR, rule basic)
apply(rule ConditionF)
apply(rule impR, rule conjL, rule basic)
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def, rule impR, rule basic)
apply(cut_tac b="(cv[>=]v11[|][~] DSPV1)" in Case, auto)
apply(rule ConditionT)
apply(rule impR, rule conjL, rule basic)
apply(rule Assign)
apply(simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def DSPV1_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule conjR)
apply(cut_tac P="(Real b)[>](Real 0)" in cut, auto)
apply(rule thinR, rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
apply(rule assMinA)
apply(rule Trans1, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def, rule impR, rule basic)
apply(rule ConditionF)
apply(rule impR, rule conjL, rule basic)
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def, rule impR, rule basic)
apply(rule Structure)
apply(rule CommunicationSim)
apply(simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV1_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)+
apply(rule conjR, rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV1_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)+
apply(rule Trans, simp add: v21_def v22_def eoa_def e_def ts_def tv_def t_def DSPV_def equal_less_def cv_def DSPV1_def DSPV2_def ltrans v11_def v12_def cs_def temp_def ca_def ta_def equal_greater_def)
done

end
