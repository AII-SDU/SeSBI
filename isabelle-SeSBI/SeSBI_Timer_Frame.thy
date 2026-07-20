theory SeSBI_Timer_Frame
  imports Main
begin

section \<open>Timer Table 4 proof inventory\<close>

record TimerFrame =
  timer_cmp :: nat
  timer_now :: nat
  timer_pending :: bool
  timer_mie :: bool
  timer_last_delta :: nat

definition timer_program :: "nat \<Rightarrow> TimerFrame \<Rightarrow> TimerFrame" where
  "timer_program value s =
     s\<lparr> timer_cmp := value,
        timer_pending := False,
        timer_mie := True,
        timer_last_delta := value + timer_now s \<rparr>"

lemma SeSBI_Timer_Frame_cmp_00000:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00001:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00002:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00003:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00004:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00005:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00006:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00007:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00008:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00009:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00010:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00011:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00012:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00013:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00014:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00015:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00016:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00017:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00018:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00019:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00020:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00021:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00022:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00023:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00024:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00025:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00026:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00027:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00028:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00029:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00030:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00031:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00032:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00033:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00034:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00035:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00036:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00037:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00038:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00039:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00040:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00041:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00042:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00043:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00044:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00045:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00046:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00047:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00048:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00049:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00050:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00051:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00052:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00053:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00054:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00055:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00056:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00057:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00058:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00059:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00060:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00061:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00062:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00063:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00064:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00065:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00066:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00067:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00068:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00069:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00070:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00071:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00072:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00073:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00074:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00075:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00076:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00077:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00078:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00079:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00080:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00081:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00082:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00083:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00084:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00085:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00086:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00087:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00088:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00089:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00090:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00091:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00092:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00093:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00094:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00095:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00096:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00097:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00098:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00099:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00100:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00101:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00102:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00103:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00104:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00105:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00106:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00107:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00108:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00109:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00110:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00111:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00112:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00113:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00114:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00115:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00116:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00117:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00118:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00119:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00120:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00121:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00122:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00123:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00124:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00125:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00126:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00127:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00128:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00129:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00130:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00131:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00132:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00133:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00134:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00135:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00136:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00137:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00138:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00139:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00140:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00141:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00142:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00143:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00144:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00145:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00146:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00147:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00148:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00149:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00150:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00151:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00152:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00153:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00154:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00155:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00156:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00157:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00158:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00159:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00160:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00161:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00162:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00163:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00164:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00165:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00166:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00167:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00168:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00169:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00170:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00171:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00172:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00173:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00174:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00175:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00176:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00177:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00178:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00179:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00180:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00181:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00182:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00183:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00184:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00185:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00186:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00187:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00188:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00189:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00190:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00191:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00192:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00193:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00194:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00195:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00196:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00197:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00198:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00199:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00200:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00201:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00202:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00203:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00204:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00205:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00206:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00207:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00208:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00209:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00210:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00211:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00212:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00213:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00214:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00215:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00216:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00217:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00218:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00219:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00220:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00221:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00222:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00223:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00224:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00225:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00226:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00227:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00228:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00229:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00230:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00231:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00232:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00233:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00234:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00235:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00236:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00237:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00238:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00239:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00240:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00241:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00242:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00243:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00244:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00245:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00246:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00247:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00248:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00249:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00250:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00251:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00252:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00253:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00254:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00255:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00256:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00257:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00258:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00259:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00260:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00261:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00262:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00263:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00264:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00265:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00266:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00267:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00268:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00269:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00270:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00271:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00272:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00273:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00274:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00275:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00276:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00277:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00278:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00279:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00280:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00281:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00282:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00283:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00284:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00285:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00286:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00287:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00288:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00289:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00290:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00291:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00292:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00293:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00294:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00295:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00296:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00297:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00298:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00299:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00300:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00301:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00302:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00303:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00304:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00305:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00306:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00307:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00308:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00309:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00310:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00311:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00312:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00313:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00314:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00315:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00316:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00317:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00318:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00319:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00320:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00321:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00322:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00323:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00324:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00325:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00326:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00327:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00328:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00329:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00330:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00331:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00332:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00333:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00334:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00335:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00336:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00337:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00338:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00339:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00340:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00341:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00342:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00343:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00344:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00345:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00346:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00347:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00348:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00349:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00350:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00351:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00352:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00353:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00354:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00355:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00356:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00357:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00358:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00359:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00360:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00361:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00362:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00363:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00364:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00365:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00366:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00367:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00368:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00369:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00370:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00371:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00372:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00373:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00374:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00375:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00376:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00377:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00378:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00379:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00380:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00381:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00382:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00383:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00384:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00385:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00386:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00387:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00388:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00389:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00390:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00391:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00392:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00393:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00394:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00395:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00396:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00397:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00398:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00399:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00400:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00401:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00402:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00403:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00404:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00405:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00406:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00407:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00408:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00409:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00410:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00411:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00412:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00413:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00414:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00415:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00416:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00417:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00418:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00419:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00420:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00421:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00422:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00423:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00424:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00425:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00426:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00427:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00428:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00429:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00430:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00431:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00432:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00433:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00434:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00435:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00436:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00437:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00438:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00439:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00440:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00441:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00442:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00443:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00444:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00445:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00446:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00447:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00448:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00449:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00450:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00451:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00452:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00453:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00454:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00455:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00456:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00457:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00458:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00459:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00460:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00461:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00462:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00463:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00464:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00465:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00466:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00467:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00468:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00469:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00470:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00471:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00472:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00473:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00474:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00475:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00476:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00477:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00478:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00479:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00480:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00481:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00482:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00483:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00484:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00485:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00486:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00487:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00488:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00489:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00490:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00491:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00492:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00493:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00494:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00495:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00496:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00497:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00498:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00499:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00500:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00501:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00502:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00503:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00504:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00505:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00506:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00507:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00508:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00509:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00510:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00511:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00512:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00513:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00514:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00515:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00516:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00517:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00518:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00519:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00520:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00521:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00522:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00523:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00524:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00525:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00526:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00527:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00528:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00529:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00530:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00531:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00532:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00533:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00534:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00535:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00536:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00537:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00538:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00539:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00540:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00541:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00542:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00543:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00544:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00545:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00546:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00547:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00548:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00549:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00550:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00551:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00552:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00553:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00554:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00555:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00556:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00557:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00558:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00559:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00560:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00561:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00562:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00563:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00564:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00565:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00566:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00567:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00568:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00569:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00570:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00571:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00572:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00573:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00574:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00575:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00576:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00577:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00578:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00579:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00580:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00581:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00582:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00583:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00584:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00585:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00586:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00587:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00588:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00589:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00590:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00591:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00592:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00593:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00594:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00595:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00596:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00597:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00598:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00599:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00600:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00601:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00602:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00603:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00604:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00605:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00606:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00607:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00608:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00609:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00610:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00611:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00612:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00613:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00614:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00615:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00616:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00617:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00618:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00619:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00620:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00621:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00622:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00623:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00624:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00625:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00626:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00627:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00628:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00629:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00630:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00631:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00632:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00633:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00634:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00635:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00636:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00637:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00638:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00639:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00640:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00641:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00642:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00643:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00644:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00645:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00646:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00647:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00648:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00649:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00650:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00651:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00652:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00653:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00654:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00655:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00656:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00657:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00658:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00659:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00660:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00661:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00662:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00663:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00664:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00665:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00666:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00667:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00668:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00669:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00670:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00671:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00672:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00673:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00674:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00675:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00676:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00677:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00678:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00679:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00680:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00681:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00682:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00683:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00684:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00685:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00686:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00687:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00688:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00689:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00690:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00691:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00692:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00693:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00694:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00695:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00696:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00697:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00698:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00699:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00700:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00701:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00702:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00703:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00704:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00705:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00706:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00707:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00708:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00709:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00710:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00711:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00712:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00713:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00714:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00715:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00716:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00717:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00718:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00719:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00720:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00721:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00722:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00723:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00724:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00725:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00726:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00727:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00728:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00729:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00730:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00731:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00732:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00733:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00734:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00735:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00736:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00737:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00738:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00739:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00740:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00741:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00742:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00743:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00744:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00745:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00746:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00747:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00748:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00749:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00750:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00751:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00752:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00753:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00754:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00755:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00756:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00757:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00758:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00759:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00760:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00761:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00762:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00763:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00764:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00765:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00766:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00767:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00768:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00769:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00770:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00771:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00772:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00773:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00774:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00775:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00776:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00777:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00778:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00779:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00780:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00781:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00782:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00783:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00784:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00785:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00786:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00787:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00788:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00789:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00790:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00791:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00792:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00793:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00794:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00795:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00796:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00797:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00798:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00799:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00800:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00801:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00802:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00803:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00804:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00805:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00806:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00807:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00808:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00809:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00810:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00811:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00812:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00813:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00814:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00815:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00816:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00817:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00818:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00819:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00820:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00821:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00822:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00823:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00824:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00825:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00826:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00827:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00828:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00829:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00830:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00831:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00832:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00833:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00834:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00835:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00836:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00837:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00838:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00839:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00840:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00841:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00842:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00843:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00844:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00845:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00846:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00847:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00848:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00849:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00850:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00851:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00852:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00853:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00854:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00855:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00856:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00857:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00858:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00859:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00860:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00861:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00862:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00863:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00864:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00865:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00866:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00867:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00868:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00869:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00870:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00871:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00872:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00873:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00874:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00875:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00876:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00877:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00878:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00879:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00880:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00881:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00882:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00883:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00884:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00885:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00886:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00887:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00888:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00889:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00890:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00891:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00892:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00893:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00894:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00895:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00896:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00897:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00898:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00899:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00900:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00901:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00902:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00903:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00904:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00905:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00906:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00907:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00908:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00909:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00910:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00911:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00912:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00913:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00914:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00915:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00916:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00917:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00918:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00919:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00920:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00921:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00922:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00923:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00924:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00925:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00926:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00927:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00928:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00929:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00930:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00931:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00932:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00933:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00934:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00935:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00936:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00937:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00938:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00939:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00940:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00941:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00942:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00943:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00944:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00945:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00946:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00947:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00948:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00949:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00950:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00951:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00952:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00953:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00954:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00955:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00956:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00957:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00958:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00959:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00960:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00961:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00962:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00963:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00964:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00965:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00966:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00967:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00968:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00969:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00970:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00971:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00972:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00973:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00974:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00975:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00976:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00977:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00978:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00979:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00980:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00981:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00982:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00983:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00984:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00985:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00986:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00987:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00988:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00989:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00990:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00991:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00992:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00993:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00994:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_00995:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_00996:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_00997:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_00998:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_00999:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01000:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01001:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01002:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01003:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01004:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01005:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01006:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01007:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01008:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01009:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01010:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01011:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01012:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01013:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01014:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01015:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01016:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01017:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01018:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01019:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01020:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01021:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01022:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01023:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01024:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01025:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01026:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01027:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01028:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01029:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01030:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01031:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01032:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01033:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01034:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01035:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01036:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01037:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01038:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01039:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01040:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01041:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01042:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01043:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01044:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01045:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01046:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01047:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01048:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01049:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01050:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01051:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01052:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01053:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01054:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01055:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01056:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01057:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01058:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01059:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01060:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01061:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01062:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01063:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01064:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01065:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01066:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01067:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01068:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01069:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01070:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01071:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01072:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01073:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01074:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01075:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01076:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01077:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01078:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01079:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01080:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01081:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01082:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01083:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01084:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01085:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01086:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01087:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01088:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01089:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01090:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01091:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01092:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01093:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01094:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01095:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01096:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01097:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01098:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01099:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01100:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01101:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01102:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01103:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01104:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01105:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01106:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01107:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01108:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01109:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01110:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01111:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01112:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01113:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01114:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01115:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01116:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01117:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01118:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01119:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01120:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01121:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01122:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01123:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01124:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01125:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01126:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01127:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01128:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01129:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01130:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01131:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01132:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01133:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01134:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01135:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01136:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01137:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01138:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01139:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01140:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01141:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01142:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01143:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01144:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01145:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01146:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01147:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01148:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01149:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01150:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01151:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01152:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01153:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01154:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01155:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01156:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01157:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01158:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01159:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01160:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01161:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01162:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01163:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01164:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01165:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01166:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01167:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01168:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01169:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01170:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01171:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01172:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01173:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01174:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01175:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01176:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01177:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01178:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01179:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01180:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01181:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01182:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01183:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01184:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01185:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01186:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01187:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01188:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01189:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01190:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01191:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01192:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01193:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01194:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01195:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01196:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01197:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01198:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01199:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01200:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01201:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01202:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01203:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01204:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01205:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01206:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01207:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01208:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01209:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01210:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01211:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01212:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01213:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01214:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01215:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01216:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01217:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01218:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01219:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01220:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01221:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01222:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01223:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01224:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01225:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01226:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01227:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01228:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01229:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01230:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01231:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01232:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01233:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01234:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01235:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01236:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01237:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01238:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01239:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01240:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01241:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01242:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01243:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01244:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01245:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01246:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01247:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01248:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01249:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01250:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01251:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01252:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01253:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01254:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01255:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01256:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01257:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01258:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01259:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01260:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01261:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01262:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01263:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01264:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01265:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01266:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01267:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01268:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01269:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01270:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01271:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01272:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01273:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01274:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01275:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01276:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01277:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01278:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01279:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01280:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01281:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01282:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01283:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01284:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01285:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01286:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01287:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01288:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01289:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01290:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01291:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01292:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01293:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01294:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01295:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01296:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01297:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01298:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01299:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01300:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01301:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01302:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01303:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01304:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01305:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01306:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01307:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01308:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01309:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01310:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01311:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01312:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01313:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01314:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01315:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01316:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01317:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01318:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01319:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01320:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01321:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01322:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01323:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01324:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01325:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01326:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01327:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01328:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01329:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01330:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01331:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01332:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01333:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01334:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01335:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01336:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01337:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01338:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01339:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01340:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01341:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01342:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01343:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01344:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01345:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01346:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01347:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01348:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01349:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01350:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01351:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01352:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01353:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01354:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01355:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01356:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01357:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01358:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01359:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01360:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01361:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01362:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01363:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01364:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01365:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01366:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01367:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01368:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01369:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01370:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01371:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01372:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01373:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01374:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01375:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01376:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01377:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01378:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01379:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01380:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01381:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01382:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01383:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01384:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01385:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01386:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01387:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01388:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01389:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01390:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01391:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01392:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01393:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01394:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01395:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01396:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01397:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01398:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01399:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01400:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01401:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01402:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01403:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01404:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01405:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01406:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01407:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01408:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01409:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01410:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01411:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01412:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01413:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01414:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01415:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01416:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01417:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01418:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01419:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01420:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01421:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01422:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01423:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01424:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01425:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01426:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01427:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01428:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01429:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01430:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01431:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01432:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01433:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01434:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01435:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01436:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01437:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01438:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01439:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01440:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01441:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01442:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01443:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01444:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01445:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01446:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01447:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01448:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01449:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01450:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01451:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01452:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01453:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01454:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01455:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01456:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01457:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01458:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01459:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01460:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01461:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01462:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01463:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01464:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01465:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01466:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01467:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01468:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01469:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01470:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01471:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01472:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01473:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01474:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01475:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01476:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01477:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01478:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01479:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01480:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01481:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01482:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01483:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01484:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01485:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01486:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01487:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01488:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01489:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01490:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01491:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01492:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01493:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01494:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01495:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01496:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01497:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01498:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01499:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01500:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01501:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01502:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01503:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01504:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01505:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01506:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01507:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01508:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01509:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01510:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01511:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01512:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01513:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01514:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01515:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01516:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01517:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01518:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01519:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01520:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01521:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01522:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01523:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01524:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01525:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01526:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01527:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01528:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01529:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01530:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01531:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01532:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01533:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01534:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01535:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01536:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01537:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01538:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01539:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01540:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01541:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01542:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01543:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01544:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01545:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01546:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01547:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01548:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01549:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01550:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01551:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01552:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01553:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01554:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01555:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01556:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01557:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01558:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01559:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01560:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01561:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01562:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01563:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01564:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01565:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01566:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01567:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01568:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01569:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01570:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01571:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01572:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01573:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01574:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01575:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01576:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01577:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01578:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01579:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01580:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01581:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01582:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01583:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01584:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01585:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01586:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01587:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01588:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01589:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01590:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01591:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01592:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01593:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01594:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01595:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01596:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01597:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01598:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01599:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01600:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01601:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01602:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01603:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01604:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01605:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01606:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01607:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01608:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01609:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01610:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01611:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01612:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01613:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01614:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01615:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01616:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01617:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01618:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01619:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01620:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01621:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01622:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01623:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01624:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01625:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01626:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01627:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01628:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01629:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01630:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01631:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01632:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01633:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01634:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01635:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01636:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01637:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01638:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01639:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01640:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01641:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01642:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01643:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01644:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01645:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01646:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01647:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01648:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01649:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01650:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01651:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01652:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01653:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01654:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01655:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01656:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01657:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01658:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01659:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01660:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01661:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01662:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01663:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01664:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01665:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01666:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01667:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01668:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01669:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01670:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01671:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01672:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01673:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01674:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01675:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01676:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01677:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01678:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01679:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01680:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01681:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01682:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01683:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01684:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01685:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01686:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01687:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01688:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01689:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01690:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01691:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01692:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01693:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01694:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01695:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01696:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01697:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01698:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01699:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01700:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01701:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01702:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01703:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01704:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01705:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01706:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01707:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01708:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01709:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01710:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01711:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01712:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01713:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01714:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01715:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01716:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01717:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01718:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01719:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01720:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01721:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01722:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01723:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01724:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01725:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01726:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01727:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01728:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01729:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01730:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01731:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01732:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01733:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01734:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01735:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01736:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01737:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01738:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01739:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01740:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01741:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01742:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01743:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01744:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01745:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01746:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01747:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01748:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01749:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01750:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01751:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01752:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01753:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01754:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01755:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01756:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01757:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01758:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01759:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01760:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01761:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01762:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01763:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01764:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01765:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01766:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01767:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01768:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01769:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01770:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01771:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01772:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01773:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01774:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01775:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01776:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01777:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01778:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01779:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01780:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01781:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01782:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01783:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01784:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01785:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01786:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01787:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01788:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01789:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01790:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01791:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01792:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01793:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01794:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01795:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01796:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01797:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01798:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01799:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01800:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01801:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01802:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01803:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01804:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01805:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01806:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01807:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01808:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01809:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01810:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01811:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01812:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01813:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01814:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01815:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01816:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01817:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01818:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01819:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01820:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01821:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01822:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01823:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01824:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01825:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01826:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01827:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01828:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01829:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01830:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01831:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01832:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01833:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01834:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01835:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01836:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01837:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01838:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01839:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01840:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01841:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01842:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01843:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01844:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01845:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01846:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01847:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01848:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01849:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01850:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01851:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01852:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01853:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01854:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01855:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01856:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01857:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01858:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01859:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01860:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01861:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01862:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01863:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01864:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01865:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01866:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01867:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01868:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01869:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01870:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01871:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01872:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01873:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01874:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01875:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01876:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01877:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01878:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01879:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01880:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01881:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01882:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01883:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01884:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01885:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01886:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01887:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01888:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01889:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01890:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01891:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01892:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01893:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01894:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01895:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01896:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01897:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01898:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01899:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01900:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01901:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01902:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01903:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01904:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01905:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01906:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01907:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01908:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01909:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01910:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01911:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01912:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01913:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01914:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01915:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01916:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01917:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01918:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01919:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01920:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01921:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01922:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01923:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01924:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01925:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01926:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01927:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01928:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01929:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01930:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01931:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01932:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01933:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01934:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01935:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01936:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01937:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01938:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01939:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01940:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01941:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01942:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01943:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01944:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01945:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01946:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01947:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01948:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01949:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01950:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01951:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01952:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01953:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01954:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01955:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01956:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01957:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01958:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01959:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01960:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01961:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01962:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01963:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01964:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01965:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01966:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01967:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01968:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01969:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01970:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01971:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01972:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01973:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01974:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01975:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01976:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01977:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01978:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01979:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01980:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01981:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01982:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01983:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01984:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01985:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01986:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01987:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01988:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01989:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01990:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01991:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01992:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01993:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01994:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_01995:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_01996:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_01997:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_01998:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_01999:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02000:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02001:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02002:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02003:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02004:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02005:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02006:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02007:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02008:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02009:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02010:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02011:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02012:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02013:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02014:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02015:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02016:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02017:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02018:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02019:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02020:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02021:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02022:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02023:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02024:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02025:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02026:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02027:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02028:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02029:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02030:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02031:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02032:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02033:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02034:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02035:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02036:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02037:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02038:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02039:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02040:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02041:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02042:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02043:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02044:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02045:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02046:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02047:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02048:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02049:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02050:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02051:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02052:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02053:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02054:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02055:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02056:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02057:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02058:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02059:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02060:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02061:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02062:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02063:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02064:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02065:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02066:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02067:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02068:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02069:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02070:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02071:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02072:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02073:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02074:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02075:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02076:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02077:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02078:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02079:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02080:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02081:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02082:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02083:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02084:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02085:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02086:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02087:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02088:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02089:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02090:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02091:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02092:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02093:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02094:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_cmp_02095:
  shows
    "timer_cmp (timer_program value s) = value"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_pending_02096:
  shows
    "timer_pending (timer_program value s) = False"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_mie_02097:
  shows
    "timer_mie (timer_program value s) = True"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_now_02098:
  shows
    "timer_now (timer_program value s) = timer_now s"
  by (simp add: timer_program_def)

lemma SeSBI_Timer_Frame_delta_02099:
  shows
    "timer_last_delta (timer_program value s) = value + timer_now s"
  by (simp add: timer_program_def)

lemmas SeSBI_Timer_Frame_anchor_00000 = refl
lemmas SeSBI_Timer_Frame_anchor_00001 = refl
lemmas SeSBI_Timer_Frame_anchor_00002 = refl
end
