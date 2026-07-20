theory SeSBI_Console_Frame
  imports Main
begin

section \<open>Console Table 4 proof inventory\<close>

record ConsoleFrame =
  console_last :: nat
  console_count :: nat
  console_ready :: bool

definition console_putchar :: "nat \<Rightarrow> ConsoleFrame \<Rightarrow> ConsoleFrame" where
  "console_putchar ch s =
     s\<lparr> console_last := ch mod 256,
        console_count := Suc (console_count s),
        console_ready := True \<rparr>"

lemma SeSBI_Console_Frame_last_00000:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00001:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00002:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00003:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00004:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00005:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00006:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00007:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00008:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00009:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00010:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00011:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00012:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00013:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00014:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00015:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00016:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00017:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00018:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00019:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00020:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00021:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00022:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00023:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00024:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00025:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00026:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00027:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00028:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00029:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00030:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00031:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00032:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00033:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00034:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00035:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00036:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00037:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00038:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00039:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00040:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00041:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00042:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00043:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00044:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00045:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00046:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00047:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00048:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00049:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00050:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_last_00051:
  shows
    "console_last (console_putchar ch s) = ch mod 256"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_count_00052:
  shows
    "console_count (console_putchar ch s) = Suc (console_count s)"
  by (simp add: console_putchar_def)

lemma SeSBI_Console_Frame_ready_00053:
  shows
    "console_ready (console_putchar ch s) = True"
  by (simp add: console_putchar_def)

end
