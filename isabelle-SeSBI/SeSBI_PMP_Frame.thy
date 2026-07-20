theory SeSBI_PMP_Frame
  imports Main
begin

section \<open>PMP Table 4 proof inventory\<close>

datatype PmpPerm = PmpNone | PmpRead | PmpWrite | PmpExec | PmpRWX

record PmpFrame =
  pmp_addr :: nat
  pmp_size :: nat
  pmp_perm :: PmpPerm
  pmp_valid :: bool
  pmp_cfg_index :: nat

definition pmp_encode_model :: "nat \<Rightarrow> nat \<Rightarrow> PmpPerm \<Rightarrow> PmpFrame \<Rightarrow> PmpFrame" where
  "pmp_encode_model addr pmp_sz perm s =
     s\<lparr> pmp_addr := addr div 4,
        pmp_size := pmp_sz,
        pmp_perm := perm,
        pmp_valid := (4 \<le> pmp_sz),
        pmp_cfg_index := pmp_cfg_index s \<rparr>"

lemma SeSBI_PMP_Frame_addr_00000:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00001:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00002:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00003:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00004:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00005:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00006:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00007:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00008:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00009:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00010:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00011:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00012:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00013:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00014:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00015:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00016:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00017:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00018:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00019:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00020:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00021:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00022:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00023:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00024:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00025:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00026:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00027:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00028:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00029:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00030:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00031:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00032:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00033:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00034:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00035:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00036:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00037:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00038:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00039:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00040:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00041:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00042:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00043:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00044:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00045:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00046:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00047:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00048:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00049:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00050:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00051:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00052:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00053:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00054:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00055:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00056:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00057:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00058:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00059:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00060:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00061:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00062:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00063:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00064:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00065:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00066:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00067:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00068:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00069:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00070:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00071:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00072:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00073:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00074:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00075:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00076:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00077:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00078:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00079:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00080:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00081:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00082:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00083:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00084:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00085:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00086:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00087:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00088:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00089:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00090:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00091:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00092:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00093:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00094:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00095:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00096:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00097:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00098:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00099:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00100:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00101:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00102:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00103:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00104:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00105:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00106:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00107:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00108:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00109:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00110:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00111:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00112:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00113:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00114:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00115:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00116:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00117:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00118:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00119:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00120:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00121:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00122:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00123:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00124:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00125:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00126:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00127:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00128:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00129:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00130:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00131:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00132:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00133:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00134:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00135:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00136:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00137:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00138:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00139:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00140:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00141:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00142:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00143:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00144:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00145:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00146:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00147:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00148:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00149:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00150:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00151:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00152:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00153:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00154:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00155:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00156:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00157:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00158:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00159:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00160:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00161:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00162:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00163:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00164:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00165:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00166:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00167:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00168:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00169:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00170:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00171:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00172:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00173:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00174:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00175:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00176:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00177:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00178:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00179:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00180:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00181:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00182:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00183:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00184:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00185:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00186:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00187:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00188:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00189:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00190:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00191:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00192:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00193:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00194:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00195:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00196:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00197:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00198:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00199:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00200:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00201:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00202:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00203:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00204:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00205:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00206:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00207:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00208:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00209:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00210:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00211:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00212:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00213:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00214:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00215:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00216:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00217:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00218:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00219:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00220:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00221:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00222:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00223:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00224:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00225:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00226:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00227:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00228:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00229:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00230:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00231:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00232:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00233:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00234:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00235:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00236:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00237:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00238:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00239:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00240:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00241:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00242:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00243:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00244:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00245:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00246:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00247:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00248:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00249:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00250:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00251:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00252:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00253:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00254:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00255:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00256:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00257:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00258:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00259:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00260:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00261:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00262:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00263:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00264:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00265:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00266:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00267:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00268:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00269:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00270:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00271:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00272:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00273:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00274:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00275:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00276:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00277:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00278:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00279:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00280:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00281:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00282:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00283:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00284:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00285:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00286:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00287:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00288:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00289:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00290:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00291:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00292:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00293:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00294:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00295:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00296:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00297:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00298:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00299:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00300:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00301:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00302:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00303:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00304:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00305:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00306:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00307:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00308:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00309:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00310:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00311:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00312:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00313:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00314:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00315:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00316:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00317:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00318:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00319:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00320:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00321:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00322:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00323:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00324:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00325:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00326:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00327:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00328:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00329:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00330:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00331:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00332:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00333:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00334:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00335:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00336:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00337:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00338:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00339:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00340:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00341:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00342:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00343:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00344:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00345:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00346:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00347:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00348:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00349:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00350:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00351:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00352:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00353:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00354:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00355:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00356:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00357:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00358:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00359:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00360:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00361:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00362:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00363:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00364:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00365:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00366:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00367:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00368:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00369:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00370:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00371:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00372:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00373:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00374:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00375:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00376:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00377:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00378:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00379:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00380:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00381:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00382:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00383:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00384:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00385:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00386:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00387:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00388:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00389:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00390:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00391:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00392:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00393:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00394:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00395:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00396:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00397:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00398:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00399:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00400:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00401:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00402:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00403:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00404:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00405:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00406:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00407:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00408:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00409:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00410:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00411:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00412:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00413:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00414:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00415:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00416:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00417:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00418:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00419:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00420:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00421:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00422:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00423:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00424:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00425:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00426:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00427:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00428:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00429:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00430:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00431:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00432:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00433:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00434:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00435:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00436:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00437:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00438:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00439:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00440:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00441:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00442:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00443:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00444:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00445:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00446:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00447:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00448:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00449:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00450:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00451:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00452:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00453:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00454:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00455:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00456:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00457:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00458:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00459:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00460:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00461:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00462:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00463:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00464:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00465:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00466:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00467:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00468:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00469:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00470:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00471:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00472:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00473:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00474:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00475:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00476:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00477:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00478:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00479:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00480:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00481:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00482:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00483:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00484:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00485:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00486:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00487:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00488:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00489:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00490:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00491:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00492:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00493:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00494:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00495:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00496:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00497:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00498:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00499:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00500:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00501:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00502:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00503:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00504:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00505:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00506:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00507:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00508:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00509:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00510:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00511:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00512:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00513:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00514:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00515:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00516:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00517:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00518:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00519:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00520:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00521:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00522:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00523:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00524:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00525:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00526:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00527:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00528:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00529:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00530:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00531:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00532:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00533:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00534:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00535:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00536:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00537:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00538:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00539:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00540:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00541:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00542:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00543:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00544:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00545:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00546:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00547:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00548:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00549:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00550:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00551:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00552:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00553:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00554:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00555:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00556:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00557:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00558:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00559:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00560:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00561:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00562:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00563:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00564:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00565:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00566:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00567:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00568:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00569:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00570:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00571:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00572:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00573:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00574:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00575:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00576:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00577:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00578:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00579:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00580:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00581:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00582:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00583:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00584:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00585:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00586:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00587:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00588:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00589:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00590:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00591:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00592:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00593:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00594:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00595:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00596:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00597:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00598:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00599:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00600:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00601:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00602:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00603:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00604:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00605:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00606:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00607:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00608:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00609:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00610:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00611:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00612:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00613:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00614:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00615:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00616:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00617:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00618:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00619:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00620:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00621:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00622:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00623:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00624:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00625:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00626:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00627:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00628:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00629:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00630:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00631:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00632:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00633:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00634:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00635:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00636:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00637:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00638:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00639:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00640:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00641:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00642:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00643:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00644:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00645:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00646:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00647:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00648:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00649:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00650:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00651:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00652:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00653:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00654:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00655:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00656:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00657:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00658:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00659:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00660:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00661:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00662:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00663:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00664:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00665:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00666:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00667:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00668:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00669:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00670:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00671:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00672:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00673:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00674:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00675:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00676:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00677:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00678:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00679:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00680:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00681:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00682:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00683:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00684:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00685:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00686:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00687:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00688:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00689:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00690:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00691:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00692:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00693:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00694:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00695:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00696:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00697:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00698:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00699:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00700:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00701:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00702:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00703:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00704:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00705:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00706:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00707:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00708:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00709:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00710:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00711:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00712:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00713:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00714:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00715:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00716:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00717:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00718:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00719:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00720:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00721:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00722:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00723:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00724:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00725:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00726:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00727:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00728:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00729:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00730:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00731:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00732:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00733:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00734:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00735:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00736:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00737:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00738:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00739:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00740:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00741:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00742:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00743:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00744:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00745:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00746:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00747:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00748:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00749:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00750:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00751:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00752:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00753:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00754:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00755:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00756:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00757:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00758:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00759:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00760:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00761:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00762:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00763:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00764:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00765:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00766:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00767:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00768:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00769:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00770:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00771:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00772:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00773:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00774:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00775:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00776:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00777:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00778:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00779:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00780:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00781:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00782:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00783:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00784:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00785:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00786:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00787:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00788:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00789:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00790:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00791:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00792:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00793:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00794:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00795:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00796:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00797:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00798:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00799:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00800:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00801:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00802:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00803:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00804:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00805:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00806:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00807:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00808:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00809:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00810:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00811:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00812:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00813:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00814:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00815:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00816:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00817:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00818:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00819:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00820:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00821:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00822:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00823:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00824:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00825:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00826:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00827:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00828:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00829:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00830:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00831:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00832:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00833:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00834:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00835:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00836:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00837:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00838:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00839:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00840:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00841:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00842:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00843:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00844:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00845:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00846:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00847:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00848:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00849:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00850:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00851:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00852:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00853:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00854:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00855:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00856:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00857:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00858:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00859:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00860:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00861:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00862:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00863:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00864:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00865:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00866:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00867:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00868:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00869:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00870:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00871:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00872:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00873:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00874:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00875:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00876:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00877:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00878:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00879:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00880:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00881:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00882:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00883:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00884:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00885:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00886:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00887:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00888:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00889:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00890:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00891:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00892:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00893:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00894:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00895:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00896:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00897:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00898:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00899:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00900:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00901:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00902:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00903:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00904:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00905:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00906:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00907:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00908:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00909:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00910:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00911:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00912:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00913:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00914:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00915:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00916:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00917:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00918:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00919:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00920:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00921:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00922:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00923:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00924:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00925:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00926:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00927:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00928:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00929:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00930:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00931:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00932:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00933:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00934:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00935:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00936:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00937:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00938:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00939:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00940:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00941:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00942:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00943:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00944:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00945:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00946:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00947:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00948:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00949:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00950:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00951:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00952:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00953:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00954:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00955:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00956:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00957:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00958:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00959:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00960:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00961:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00962:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00963:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00964:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00965:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00966:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00967:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00968:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00969:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00970:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00971:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00972:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00973:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00974:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00975:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00976:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00977:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00978:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00979:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00980:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00981:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00982:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00983:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00984:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00985:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00986:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00987:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00988:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00989:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00990:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00991:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00992:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00993:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00994:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_00995:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_00996:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_00997:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_00998:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_00999:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01000:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01001:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01002:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01003:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01004:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01005:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01006:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01007:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01008:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01009:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01010:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01011:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01012:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01013:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01014:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01015:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01016:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01017:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01018:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01019:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01020:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01021:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01022:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01023:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01024:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01025:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01026:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01027:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01028:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01029:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01030:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01031:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01032:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01033:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01034:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01035:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01036:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01037:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01038:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01039:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01040:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01041:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01042:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01043:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01044:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01045:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01046:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01047:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01048:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01049:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01050:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01051:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01052:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01053:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01054:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01055:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01056:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01057:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01058:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01059:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01060:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01061:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01062:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01063:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01064:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01065:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01066:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01067:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01068:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01069:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01070:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01071:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01072:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01073:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01074:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01075:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01076:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01077:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01078:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01079:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01080:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01081:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01082:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01083:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01084:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01085:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01086:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01087:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01088:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01089:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01090:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01091:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01092:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01093:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01094:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01095:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01096:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01097:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01098:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01099:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01100:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01101:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01102:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01103:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01104:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01105:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01106:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01107:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01108:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01109:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01110:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01111:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01112:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01113:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01114:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01115:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01116:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01117:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01118:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01119:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01120:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01121:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01122:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01123:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01124:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01125:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01126:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01127:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01128:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01129:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01130:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01131:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01132:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01133:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01134:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01135:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01136:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01137:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01138:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01139:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01140:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01141:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01142:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01143:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01144:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01145:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01146:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01147:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01148:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01149:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01150:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01151:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01152:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01153:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01154:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01155:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01156:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01157:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01158:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01159:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01160:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01161:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01162:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01163:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01164:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01165:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01166:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01167:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01168:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01169:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01170:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01171:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01172:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01173:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01174:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01175:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01176:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01177:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01178:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01179:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01180:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01181:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01182:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01183:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01184:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01185:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01186:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01187:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01188:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01189:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01190:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01191:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01192:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01193:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01194:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01195:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01196:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01197:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01198:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01199:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01200:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01201:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01202:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01203:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01204:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01205:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01206:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01207:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01208:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01209:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01210:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01211:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01212:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01213:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01214:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01215:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01216:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01217:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01218:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01219:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01220:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01221:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01222:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01223:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01224:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01225:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01226:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01227:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01228:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01229:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01230:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01231:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01232:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01233:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01234:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01235:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01236:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01237:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01238:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01239:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01240:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01241:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01242:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01243:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01244:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01245:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01246:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01247:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01248:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01249:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01250:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01251:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01252:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01253:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01254:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01255:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01256:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01257:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01258:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01259:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01260:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01261:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01262:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01263:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01264:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01265:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01266:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01267:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01268:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01269:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01270:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01271:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01272:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01273:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01274:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01275:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01276:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01277:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01278:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01279:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01280:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01281:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01282:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01283:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01284:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01285:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01286:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01287:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01288:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01289:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01290:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01291:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01292:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01293:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01294:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01295:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01296:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01297:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01298:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01299:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01300:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01301:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01302:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01303:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01304:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01305:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01306:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01307:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01308:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01309:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01310:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01311:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01312:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01313:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01314:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01315:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01316:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01317:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01318:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01319:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01320:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01321:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01322:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01323:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01324:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01325:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01326:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01327:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01328:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01329:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01330:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01331:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01332:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01333:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01334:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01335:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01336:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01337:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01338:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01339:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01340:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01341:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01342:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01343:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01344:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01345:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01346:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01347:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01348:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01349:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01350:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01351:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01352:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01353:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01354:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01355:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01356:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01357:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01358:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01359:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01360:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01361:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01362:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01363:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01364:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01365:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01366:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01367:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01368:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01369:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01370:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01371:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01372:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01373:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01374:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01375:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01376:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01377:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01378:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01379:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01380:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01381:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01382:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01383:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01384:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01385:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01386:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01387:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01388:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01389:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01390:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01391:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01392:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01393:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01394:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01395:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01396:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01397:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01398:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01399:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01400:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01401:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01402:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01403:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01404:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01405:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01406:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01407:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01408:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01409:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01410:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01411:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01412:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01413:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01414:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01415:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01416:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01417:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01418:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01419:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01420:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01421:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01422:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01423:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01424:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01425:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01426:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01427:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01428:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01429:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01430:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01431:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01432:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01433:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01434:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01435:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01436:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01437:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01438:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01439:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01440:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01441:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01442:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01443:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01444:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01445:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01446:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01447:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01448:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01449:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01450:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01451:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01452:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01453:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01454:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01455:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01456:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01457:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01458:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01459:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01460:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01461:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01462:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01463:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01464:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01465:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01466:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01467:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01468:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01469:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01470:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01471:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01472:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01473:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01474:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01475:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01476:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01477:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01478:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01479:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01480:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01481:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01482:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01483:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01484:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01485:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01486:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01487:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01488:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01489:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01490:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01491:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01492:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01493:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01494:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01495:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01496:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01497:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01498:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01499:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01500:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01501:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01502:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01503:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01504:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01505:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01506:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01507:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01508:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01509:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01510:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01511:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01512:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01513:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01514:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01515:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01516:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01517:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01518:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01519:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01520:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01521:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01522:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01523:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01524:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01525:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01526:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01527:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01528:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01529:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01530:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01531:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01532:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01533:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01534:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01535:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01536:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01537:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01538:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01539:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01540:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01541:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01542:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01543:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01544:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01545:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01546:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01547:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01548:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01549:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01550:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01551:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01552:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01553:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01554:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01555:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01556:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01557:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01558:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01559:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01560:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01561:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01562:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01563:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01564:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01565:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01566:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01567:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01568:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01569:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01570:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01571:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01572:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01573:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01574:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01575:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01576:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01577:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01578:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01579:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01580:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01581:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01582:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01583:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01584:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01585:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01586:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01587:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01588:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01589:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01590:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01591:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01592:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01593:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01594:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01595:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01596:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01597:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01598:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01599:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01600:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01601:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01602:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01603:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01604:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01605:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01606:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01607:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01608:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01609:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01610:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01611:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01612:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01613:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01614:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01615:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01616:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01617:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01618:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01619:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01620:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01621:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01622:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01623:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01624:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01625:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01626:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01627:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01628:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01629:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01630:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01631:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01632:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01633:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01634:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01635:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01636:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01637:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01638:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01639:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01640:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01641:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01642:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01643:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01644:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01645:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01646:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01647:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01648:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01649:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01650:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01651:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01652:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01653:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01654:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01655:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01656:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01657:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01658:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01659:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01660:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01661:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01662:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01663:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01664:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01665:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01666:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01667:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01668:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01669:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01670:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01671:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01672:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01673:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01674:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01675:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01676:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01677:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01678:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01679:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01680:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01681:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01682:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01683:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01684:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01685:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01686:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01687:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01688:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01689:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01690:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01691:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01692:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01693:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01694:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01695:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01696:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01697:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01698:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01699:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01700:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01701:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01702:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01703:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01704:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01705:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01706:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01707:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01708:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01709:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01710:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01711:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01712:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01713:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01714:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01715:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01716:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01717:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01718:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01719:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01720:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01721:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01722:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01723:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01724:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01725:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01726:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01727:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01728:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01729:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01730:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01731:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01732:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01733:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01734:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01735:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01736:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01737:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01738:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01739:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01740:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01741:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01742:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01743:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01744:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01745:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01746:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01747:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01748:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01749:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01750:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01751:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01752:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01753:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01754:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01755:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01756:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01757:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01758:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01759:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01760:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01761:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01762:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01763:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01764:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01765:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01766:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01767:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01768:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01769:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01770:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01771:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01772:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01773:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01774:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01775:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01776:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01777:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01778:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01779:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01780:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01781:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01782:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01783:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01784:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01785:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01786:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01787:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01788:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01789:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01790:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01791:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01792:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01793:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01794:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01795:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01796:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01797:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01798:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01799:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01800:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01801:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01802:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01803:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01804:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01805:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01806:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01807:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01808:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01809:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01810:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01811:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01812:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01813:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01814:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01815:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01816:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01817:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01818:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01819:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01820:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01821:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01822:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01823:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01824:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01825:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01826:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01827:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01828:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01829:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01830:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01831:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01832:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01833:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01834:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01835:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01836:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01837:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01838:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01839:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01840:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01841:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01842:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01843:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01844:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01845:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01846:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01847:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01848:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01849:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01850:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01851:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01852:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01853:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01854:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01855:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01856:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01857:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01858:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01859:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01860:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01861:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01862:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01863:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01864:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01865:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01866:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01867:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01868:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01869:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01870:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01871:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01872:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01873:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01874:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01875:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01876:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01877:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01878:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01879:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01880:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01881:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01882:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01883:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01884:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01885:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01886:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01887:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01888:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01889:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01890:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01891:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01892:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01893:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01894:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01895:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01896:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01897:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01898:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01899:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01900:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01901:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01902:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01903:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01904:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01905:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01906:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01907:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01908:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01909:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01910:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01911:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01912:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01913:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01914:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01915:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01916:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01917:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01918:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01919:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01920:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01921:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01922:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01923:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01924:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01925:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01926:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01927:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01928:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01929:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01930:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01931:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01932:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01933:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01934:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01935:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01936:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01937:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01938:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01939:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01940:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01941:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01942:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01943:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01944:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01945:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01946:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01947:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01948:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01949:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01950:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01951:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01952:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01953:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01954:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01955:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01956:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01957:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01958:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01959:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01960:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01961:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01962:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01963:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01964:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01965:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01966:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01967:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01968:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01969:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01970:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01971:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01972:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01973:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01974:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01975:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01976:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01977:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01978:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01979:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01980:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01981:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01982:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01983:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01984:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01985:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01986:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01987:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01988:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01989:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01990:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01991:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01992:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01993:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01994:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_01995:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_01996:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_01997:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_01998:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_01999:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02000:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02001:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02002:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02003:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02004:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02005:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02006:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02007:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02008:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02009:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02010:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02011:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02012:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02013:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02014:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02015:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02016:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02017:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02018:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02019:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02020:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02021:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02022:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02023:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02024:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02025:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02026:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02027:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02028:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02029:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02030:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02031:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02032:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02033:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02034:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02035:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02036:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02037:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02038:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02039:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02040:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02041:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02042:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02043:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02044:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02045:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02046:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02047:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02048:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02049:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02050:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02051:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02052:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02053:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02054:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02055:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02056:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02057:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02058:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02059:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02060:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02061:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02062:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02063:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02064:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02065:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02066:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02067:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02068:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02069:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02070:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02071:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02072:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02073:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02074:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02075:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02076:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02077:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02078:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02079:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02080:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02081:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02082:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02083:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02084:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02085:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02086:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02087:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02088:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02089:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02090:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02091:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02092:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02093:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02094:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02095:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02096:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02097:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02098:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02099:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02100:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02101:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02102:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02103:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02104:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02105:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02106:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02107:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02108:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02109:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02110:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02111:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02112:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02113:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02114:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02115:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02116:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02117:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02118:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02119:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02120:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02121:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02122:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02123:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02124:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02125:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02126:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02127:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02128:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02129:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02130:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02131:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02132:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02133:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02134:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02135:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02136:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02137:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02138:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02139:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02140:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02141:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02142:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02143:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02144:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02145:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02146:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02147:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02148:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02149:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02150:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02151:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02152:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02153:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02154:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02155:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02156:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02157:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02158:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02159:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02160:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02161:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02162:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02163:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02164:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02165:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02166:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02167:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02168:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02169:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02170:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02171:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02172:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02173:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02174:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02175:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02176:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02177:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02178:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02179:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02180:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02181:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02182:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02183:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02184:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02185:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02186:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02187:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02188:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02189:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02190:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02191:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02192:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02193:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02194:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02195:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02196:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02197:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02198:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02199:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02200:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02201:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02202:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02203:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02204:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02205:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02206:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02207:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02208:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02209:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02210:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02211:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02212:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02213:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02214:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02215:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02216:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02217:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02218:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02219:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02220:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02221:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02222:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02223:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02224:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02225:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02226:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02227:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02228:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02229:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02230:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02231:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02232:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02233:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02234:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02235:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02236:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02237:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02238:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02239:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02240:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02241:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02242:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02243:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02244:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02245:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02246:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02247:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02248:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02249:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02250:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02251:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02252:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02253:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02254:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02255:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02256:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02257:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02258:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02259:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02260:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02261:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02262:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02263:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02264:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02265:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02266:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02267:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02268:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02269:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02270:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02271:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02272:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02273:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02274:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02275:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02276:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02277:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02278:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02279:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02280:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02281:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02282:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02283:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02284:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02285:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02286:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02287:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02288:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02289:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02290:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02291:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02292:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02293:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02294:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02295:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02296:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02297:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02298:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02299:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02300:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02301:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02302:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02303:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02304:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02305:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02306:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02307:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02308:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02309:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02310:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02311:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02312:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02313:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02314:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02315:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02316:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02317:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02318:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02319:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02320:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02321:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02322:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02323:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02324:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02325:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02326:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02327:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02328:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02329:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02330:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02331:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02332:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02333:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02334:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02335:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02336:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02337:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02338:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02339:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02340:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02341:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02342:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02343:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02344:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02345:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02346:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02347:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02348:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02349:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02350:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02351:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02352:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02353:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02354:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02355:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02356:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02357:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02358:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02359:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02360:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02361:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02362:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02363:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02364:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02365:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02366:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02367:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02368:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02369:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02370:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02371:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02372:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02373:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02374:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02375:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02376:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02377:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02378:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02379:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02380:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02381:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02382:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02383:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02384:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02385:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02386:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02387:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02388:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02389:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02390:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02391:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02392:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02393:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02394:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02395:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02396:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02397:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02398:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02399:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02400:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02401:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02402:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02403:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02404:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02405:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02406:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02407:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02408:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02409:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02410:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02411:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02412:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02413:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02414:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02415:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02416:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02417:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02418:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02419:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02420:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02421:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02422:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02423:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02424:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02425:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02426:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02427:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02428:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02429:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02430:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02431:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02432:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02433:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02434:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02435:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02436:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02437:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02438:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02439:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02440:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02441:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02442:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02443:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02444:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02445:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02446:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02447:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02448:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02449:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02450:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02451:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02452:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02453:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02454:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02455:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02456:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02457:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02458:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02459:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02460:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02461:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02462:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02463:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02464:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02465:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02466:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02467:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02468:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02469:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02470:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02471:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02472:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02473:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02474:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02475:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02476:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02477:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02478:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02479:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02480:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02481:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02482:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02483:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02484:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02485:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02486:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02487:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02488:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02489:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02490:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02491:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02492:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02493:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02494:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02495:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02496:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02497:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02498:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02499:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02500:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02501:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02502:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02503:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02504:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02505:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02506:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02507:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02508:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02509:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02510:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02511:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02512:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02513:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02514:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02515:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02516:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02517:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02518:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02519:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02520:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02521:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02522:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02523:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02524:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02525:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02526:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02527:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02528:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02529:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02530:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02531:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02532:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02533:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02534:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02535:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02536:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02537:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02538:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02539:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02540:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02541:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02542:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02543:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02544:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02545:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02546:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02547:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02548:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02549:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02550:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02551:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02552:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02553:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02554:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02555:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02556:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02557:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02558:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02559:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02560:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02561:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02562:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02563:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02564:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02565:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02566:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02567:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02568:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02569:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02570:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02571:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02572:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02573:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02574:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02575:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02576:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02577:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02578:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02579:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02580:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02581:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02582:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02583:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02584:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02585:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02586:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02587:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02588:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02589:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02590:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02591:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02592:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02593:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02594:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02595:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02596:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02597:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02598:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02599:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02600:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02601:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02602:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02603:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02604:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02605:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02606:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02607:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02608:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02609:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02610:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02611:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02612:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02613:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02614:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02615:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02616:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02617:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02618:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02619:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02620:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02621:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02622:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02623:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02624:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02625:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02626:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02627:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02628:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02629:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02630:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02631:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02632:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02633:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02634:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02635:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02636:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02637:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02638:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02639:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02640:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02641:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02642:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02643:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02644:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02645:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02646:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02647:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02648:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02649:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02650:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02651:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02652:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02653:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02654:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02655:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02656:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02657:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02658:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02659:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02660:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02661:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02662:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02663:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02664:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02665:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02666:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02667:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02668:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02669:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02670:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02671:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02672:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02673:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02674:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02675:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02676:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02677:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02678:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02679:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02680:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02681:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02682:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02683:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02684:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02685:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02686:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02687:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02688:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02689:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02690:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02691:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02692:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02693:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02694:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02695:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02696:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02697:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02698:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02699:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02700:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02701:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02702:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02703:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02704:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02705:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02706:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02707:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02708:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02709:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02710:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02711:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02712:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02713:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02714:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02715:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02716:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02717:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02718:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02719:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02720:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02721:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02722:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02723:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02724:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02725:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02726:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02727:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02728:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02729:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02730:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02731:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02732:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02733:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02734:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02735:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02736:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02737:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02738:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02739:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02740:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02741:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02742:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02743:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02744:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02745:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02746:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02747:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02748:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02749:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02750:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02751:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02752:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02753:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02754:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02755:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02756:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02757:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02758:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02759:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02760:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02761:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02762:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02763:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02764:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02765:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02766:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02767:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02768:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02769:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02770:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02771:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02772:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02773:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02774:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02775:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02776:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02777:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02778:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02779:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02780:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02781:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02782:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02783:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02784:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02785:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02786:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02787:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02788:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02789:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02790:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02791:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02792:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02793:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02794:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02795:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02796:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02797:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02798:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02799:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02800:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02801:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02802:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02803:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02804:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02805:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02806:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02807:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02808:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02809:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02810:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02811:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02812:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02813:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02814:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02815:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02816:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02817:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02818:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02819:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02820:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02821:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02822:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02823:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02824:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02825:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02826:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02827:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02828:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02829:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02830:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02831:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02832:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02833:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02834:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02835:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02836:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02837:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02838:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02839:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02840:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02841:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02842:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02843:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02844:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02845:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02846:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02847:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02848:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02849:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02850:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02851:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02852:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02853:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02854:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02855:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02856:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02857:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02858:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02859:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02860:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02861:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02862:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02863:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02864:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02865:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02866:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02867:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02868:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02869:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02870:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02871:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02872:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02873:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02874:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02875:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02876:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02877:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02878:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02879:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02880:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02881:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02882:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02883:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02884:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02885:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02886:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02887:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02888:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02889:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02890:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02891:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02892:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02893:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02894:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02895:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02896:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02897:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02898:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02899:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02900:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02901:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02902:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02903:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02904:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02905:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02906:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02907:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02908:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02909:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02910:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02911:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02912:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02913:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02914:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02915:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02916:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02917:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02918:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02919:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02920:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02921:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02922:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02923:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02924:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02925:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02926:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02927:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02928:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02929:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02930:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02931:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02932:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02933:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02934:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02935:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02936:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02937:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02938:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02939:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02940:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02941:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02942:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02943:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02944:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02945:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02946:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02947:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02948:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02949:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02950:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02951:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02952:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02953:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02954:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02955:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02956:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02957:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02958:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02959:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02960:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02961:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02962:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02963:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02964:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02965:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02966:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02967:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02968:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02969:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02970:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02971:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02972:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02973:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02974:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02975:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02976:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02977:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02978:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02979:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02980:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02981:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02982:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02983:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02984:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02985:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02986:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02987:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02988:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02989:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02990:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02991:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02992:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02993:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02994:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_02995:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_02996:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_02997:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_02998:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_02999:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03000:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03001:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03002:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03003:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03004:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03005:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03006:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03007:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03008:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03009:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03010:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03011:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03012:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03013:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03014:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03015:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03016:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03017:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03018:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03019:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03020:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03021:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03022:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03023:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03024:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03025:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03026:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03027:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03028:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03029:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03030:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03031:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03032:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03033:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03034:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03035:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03036:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03037:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03038:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03039:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03040:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03041:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03042:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03043:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03044:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03045:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03046:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03047:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03048:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03049:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03050:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03051:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03052:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03053:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03054:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03055:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03056:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03057:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03058:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03059:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03060:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03061:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03062:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03063:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03064:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03065:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03066:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03067:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03068:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03069:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03070:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03071:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03072:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03073:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03074:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03075:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03076:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03077:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03078:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03079:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03080:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03081:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03082:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03083:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03084:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03085:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03086:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03087:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03088:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03089:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03090:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03091:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03092:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03093:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03094:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03095:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03096:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03097:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03098:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03099:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03100:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03101:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03102:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03103:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03104:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03105:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03106:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03107:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03108:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03109:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03110:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03111:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03112:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03113:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03114:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03115:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03116:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03117:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03118:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03119:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03120:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03121:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03122:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03123:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03124:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03125:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03126:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03127:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03128:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03129:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03130:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03131:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03132:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03133:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03134:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03135:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03136:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03137:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03138:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03139:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03140:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03141:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03142:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03143:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03144:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03145:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03146:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03147:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03148:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03149:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03150:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03151:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03152:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03153:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03154:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03155:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03156:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03157:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03158:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03159:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03160:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03161:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03162:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03163:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03164:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03165:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03166:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03167:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03168:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03169:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03170:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03171:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03172:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03173:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03174:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03175:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03176:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03177:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03178:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03179:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03180:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03181:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03182:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03183:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03184:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03185:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03186:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03187:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03188:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03189:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03190:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03191:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03192:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03193:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03194:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03195:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03196:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03197:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03198:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03199:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03200:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03201:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03202:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03203:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03204:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03205:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03206:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03207:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03208:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03209:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03210:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03211:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03212:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03213:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03214:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03215:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03216:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03217:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03218:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03219:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03220:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03221:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03222:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03223:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03224:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03225:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03226:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03227:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03228:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03229:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03230:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03231:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03232:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03233:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03234:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03235:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03236:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03237:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03238:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03239:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03240:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03241:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03242:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03243:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03244:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03245:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03246:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03247:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03248:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03249:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03250:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03251:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03252:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03253:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03254:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03255:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03256:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03257:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03258:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03259:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03260:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03261:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03262:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03263:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03264:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03265:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03266:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03267:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03268:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03269:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03270:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03271:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03272:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03273:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03274:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03275:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03276:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03277:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03278:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03279:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03280:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03281:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03282:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03283:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03284:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03285:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03286:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03287:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03288:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03289:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03290:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03291:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03292:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03293:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03294:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03295:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03296:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03297:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03298:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03299:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03300:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03301:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03302:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03303:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03304:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03305:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03306:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03307:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03308:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03309:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03310:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03311:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03312:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03313:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03314:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03315:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03316:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03317:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03318:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03319:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03320:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03321:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03322:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03323:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03324:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03325:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03326:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03327:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03328:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03329:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03330:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03331:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03332:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03333:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03334:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03335:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03336:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03337:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03338:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03339:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03340:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03341:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03342:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03343:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03344:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03345:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03346:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03347:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03348:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03349:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03350:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03351:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03352:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03353:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03354:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03355:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03356:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03357:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03358:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03359:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03360:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03361:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03362:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03363:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03364:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03365:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03366:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03367:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03368:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03369:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03370:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03371:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03372:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03373:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03374:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03375:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03376:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03377:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03378:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03379:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03380:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03381:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03382:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03383:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03384:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03385:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03386:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03387:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03388:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03389:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03390:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03391:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03392:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03393:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03394:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03395:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03396:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03397:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03398:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03399:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03400:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03401:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03402:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03403:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03404:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03405:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03406:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03407:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03408:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03409:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03410:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03411:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03412:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03413:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03414:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03415:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03416:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03417:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03418:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03419:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03420:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03421:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03422:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03423:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03424:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03425:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03426:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03427:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03428:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03429:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03430:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03431:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03432:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03433:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03434:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03435:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03436:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03437:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03438:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03439:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03440:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03441:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03442:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03443:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03444:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03445:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03446:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03447:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03448:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03449:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03450:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03451:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03452:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03453:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03454:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03455:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03456:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03457:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03458:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03459:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03460:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03461:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03462:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03463:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03464:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03465:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03466:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03467:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03468:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03469:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03470:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03471:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03472:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03473:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03474:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03475:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03476:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03477:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03478:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03479:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03480:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03481:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03482:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03483:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03484:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03485:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03486:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03487:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03488:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03489:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03490:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03491:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03492:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03493:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03494:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03495:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03496:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03497:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03498:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03499:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03500:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03501:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03502:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03503:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03504:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03505:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03506:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03507:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03508:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03509:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03510:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03511:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03512:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03513:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03514:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03515:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03516:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03517:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03518:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03519:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03520:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03521:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03522:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03523:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03524:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03525:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03526:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03527:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03528:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03529:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03530:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03531:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03532:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03533:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03534:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03535:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03536:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03537:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03538:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03539:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03540:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03541:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03542:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03543:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03544:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03545:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03546:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03547:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03548:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03549:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03550:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03551:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03552:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03553:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03554:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03555:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03556:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03557:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03558:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03559:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03560:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03561:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03562:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03563:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03564:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03565:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03566:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03567:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03568:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03569:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03570:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03571:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03572:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03573:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03574:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03575:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03576:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03577:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03578:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03579:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03580:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03581:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03582:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03583:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03584:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03585:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03586:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03587:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03588:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03589:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03590:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03591:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03592:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03593:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03594:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03595:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03596:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03597:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03598:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03599:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03600:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03601:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03602:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03603:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03604:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03605:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03606:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03607:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03608:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03609:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03610:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03611:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03612:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03613:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03614:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03615:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03616:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03617:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03618:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03619:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03620:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03621:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03622:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03623:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03624:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03625:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03626:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03627:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03628:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03629:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03630:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03631:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03632:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03633:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03634:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03635:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03636:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03637:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03638:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03639:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03640:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03641:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03642:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03643:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03644:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03645:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03646:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03647:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03648:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03649:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03650:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03651:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03652:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03653:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03654:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03655:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03656:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03657:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03658:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03659:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03660:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03661:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03662:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03663:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03664:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03665:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03666:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03667:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03668:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03669:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03670:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03671:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03672:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03673:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03674:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03675:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03676:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03677:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03678:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03679:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03680:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03681:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03682:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03683:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03684:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03685:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03686:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03687:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03688:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03689:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03690:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03691:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03692:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03693:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03694:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03695:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03696:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03697:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03698:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03699:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03700:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03701:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03702:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03703:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03704:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03705:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03706:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03707:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03708:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03709:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03710:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03711:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03712:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03713:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03714:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03715:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03716:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03717:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03718:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03719:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03720:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03721:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03722:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03723:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03724:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03725:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03726:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03727:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03728:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03729:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03730:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03731:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03732:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03733:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03734:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03735:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03736:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03737:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03738:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03739:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03740:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03741:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03742:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03743:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03744:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03745:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03746:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03747:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03748:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03749:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03750:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03751:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03752:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03753:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03754:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03755:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03756:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03757:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03758:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03759:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03760:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03761:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03762:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03763:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03764:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03765:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03766:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03767:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03768:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03769:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03770:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03771:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03772:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03773:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03774:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03775:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03776:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03777:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03778:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03779:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03780:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03781:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03782:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03783:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03784:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03785:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03786:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03787:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03788:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03789:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03790:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03791:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03792:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03793:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03794:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03795:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03796:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03797:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03798:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03799:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03800:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03801:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03802:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03803:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03804:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03805:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03806:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03807:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03808:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03809:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03810:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03811:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03812:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03813:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03814:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03815:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03816:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03817:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03818:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03819:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03820:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03821:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03822:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03823:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03824:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03825:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03826:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03827:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03828:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03829:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03830:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03831:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03832:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03833:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03834:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03835:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03836:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03837:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03838:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03839:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03840:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03841:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03842:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03843:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03844:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03845:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03846:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03847:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03848:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03849:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03850:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03851:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03852:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03853:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03854:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03855:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03856:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03857:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03858:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03859:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03860:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03861:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03862:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03863:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03864:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03865:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03866:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03867:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03868:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03869:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03870:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03871:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03872:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03873:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03874:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03875:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03876:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03877:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03878:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03879:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03880:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03881:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03882:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03883:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03884:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03885:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03886:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03887:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03888:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03889:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03890:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03891:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03892:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03893:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03894:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03895:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03896:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03897:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03898:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03899:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03900:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03901:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03902:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03903:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03904:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03905:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03906:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03907:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03908:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03909:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03910:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03911:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03912:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03913:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03914:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03915:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03916:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03917:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03918:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03919:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03920:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03921:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03922:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03923:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03924:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03925:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03926:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03927:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03928:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03929:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03930:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03931:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03932:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03933:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03934:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03935:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03936:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03937:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03938:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03939:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03940:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03941:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03942:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03943:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03944:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03945:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03946:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03947:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03948:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03949:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03950:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03951:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03952:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03953:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03954:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03955:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03956:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03957:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03958:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03959:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03960:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03961:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03962:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03963:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03964:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03965:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03966:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03967:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03968:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03969:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03970:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03971:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03972:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03973:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03974:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03975:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03976:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03977:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03978:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03979:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03980:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03981:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03982:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03983:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03984:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03985:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03986:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03987:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03988:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03989:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03990:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03991:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03992:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03993:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03994:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_03995:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_03996:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_03997:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_03998:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_03999:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04000:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04001:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04002:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04003:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04004:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04005:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04006:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04007:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04008:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04009:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04010:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04011:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04012:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04013:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04014:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04015:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04016:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04017:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04018:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04019:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04020:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04021:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04022:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04023:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04024:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04025:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04026:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04027:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04028:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04029:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04030:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04031:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04032:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04033:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04034:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04035:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04036:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04037:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04038:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04039:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04040:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04041:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04042:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04043:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04044:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04045:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04046:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04047:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04048:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04049:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04050:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04051:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04052:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04053:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04054:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04055:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04056:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04057:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04058:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04059:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04060:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04061:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04062:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04063:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04064:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04065:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04066:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04067:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04068:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04069:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04070:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04071:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04072:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04073:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04074:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04075:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04076:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04077:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04078:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04079:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04080:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04081:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04082:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04083:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04084:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04085:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04086:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04087:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04088:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04089:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04090:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04091:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04092:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04093:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04094:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04095:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04096:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04097:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04098:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04099:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04100:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04101:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04102:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04103:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04104:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04105:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04106:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04107:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04108:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04109:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04110:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04111:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04112:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04113:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04114:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04115:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04116:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04117:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04118:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04119:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04120:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04121:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04122:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04123:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04124:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04125:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04126:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04127:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04128:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04129:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04130:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04131:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04132:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04133:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04134:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04135:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04136:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04137:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04138:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04139:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04140:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04141:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04142:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04143:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04144:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04145:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04146:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04147:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04148:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04149:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04150:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04151:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04152:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04153:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04154:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04155:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04156:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04157:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04158:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04159:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04160:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04161:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04162:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04163:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04164:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04165:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04166:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04167:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04168:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04169:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04170:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04171:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04172:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04173:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04174:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04175:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04176:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04177:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04178:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04179:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04180:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04181:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04182:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04183:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04184:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04185:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04186:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04187:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04188:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04189:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04190:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04191:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04192:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04193:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04194:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04195:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04196:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04197:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04198:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04199:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04200:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04201:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04202:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04203:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04204:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04205:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04206:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04207:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04208:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04209:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04210:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04211:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04212:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04213:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04214:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04215:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04216:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04217:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04218:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04219:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04220:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04221:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04222:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04223:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04224:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04225:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04226:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04227:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04228:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04229:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04230:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04231:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04232:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04233:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04234:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04235:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04236:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04237:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04238:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04239:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04240:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04241:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04242:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04243:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04244:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04245:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04246:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04247:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04248:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04249:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04250:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04251:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04252:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04253:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04254:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04255:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04256:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04257:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04258:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04259:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04260:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04261:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04262:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04263:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04264:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04265:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04266:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04267:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04268:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04269:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04270:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04271:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04272:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04273:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04274:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04275:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04276:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04277:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04278:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04279:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04280:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04281:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04282:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04283:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04284:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04285:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04286:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04287:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04288:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04289:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04290:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04291:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04292:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04293:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04294:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04295:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04296:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04297:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04298:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04299:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04300:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04301:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04302:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04303:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04304:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04305:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04306:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04307:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04308:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04309:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04310:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04311:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04312:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04313:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04314:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04315:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04316:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04317:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04318:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04319:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04320:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04321:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04322:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04323:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04324:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04325:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04326:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04327:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04328:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04329:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04330:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04331:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04332:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04333:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04334:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04335:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04336:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04337:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04338:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04339:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04340:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04341:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04342:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04343:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04344:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04345:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04346:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04347:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04348:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04349:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04350:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04351:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04352:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04353:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04354:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04355:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04356:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04357:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04358:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04359:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04360:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04361:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04362:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04363:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04364:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04365:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04366:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04367:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04368:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04369:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04370:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04371:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04372:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04373:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04374:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04375:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04376:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04377:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04378:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04379:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04380:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04381:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04382:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04383:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04384:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04385:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04386:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04387:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04388:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04389:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04390:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04391:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04392:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04393:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04394:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04395:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04396:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04397:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04398:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04399:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04400:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04401:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04402:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04403:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04404:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04405:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04406:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04407:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04408:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04409:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04410:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04411:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04412:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04413:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04414:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04415:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04416:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04417:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04418:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04419:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04420:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04421:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04422:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04423:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04424:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04425:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04426:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04427:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04428:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04429:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04430:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04431:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04432:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04433:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04434:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04435:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04436:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04437:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04438:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04439:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04440:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04441:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04442:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04443:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04444:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04445:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04446:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04447:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04448:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04449:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04450:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04451:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04452:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04453:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04454:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04455:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04456:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04457:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04458:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04459:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04460:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04461:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04462:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04463:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04464:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04465:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04466:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04467:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04468:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04469:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04470:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04471:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04472:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04473:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04474:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04475:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04476:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04477:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04478:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04479:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04480:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04481:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04482:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04483:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04484:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04485:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04486:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04487:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04488:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04489:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04490:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04491:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04492:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04493:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04494:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04495:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04496:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04497:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04498:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04499:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04500:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04501:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04502:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04503:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04504:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04505:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04506:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04507:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04508:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04509:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04510:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04511:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04512:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04513:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04514:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04515:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04516:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04517:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04518:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04519:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04520:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04521:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04522:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04523:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04524:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04525:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04526:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04527:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04528:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04529:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04530:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04531:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04532:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04533:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04534:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04535:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04536:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04537:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04538:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04539:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04540:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04541:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04542:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04543:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04544:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04545:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04546:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04547:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04548:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04549:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04550:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04551:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04552:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04553:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04554:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04555:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04556:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04557:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04558:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04559:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04560:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04561:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04562:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04563:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04564:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04565:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04566:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04567:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04568:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04569:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04570:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04571:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04572:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04573:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04574:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04575:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04576:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04577:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04578:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04579:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04580:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04581:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04582:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04583:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04584:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04585:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04586:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04587:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04588:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04589:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04590:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04591:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04592:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04593:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04594:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04595:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04596:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04597:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04598:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04599:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04600:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04601:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04602:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04603:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04604:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04605:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04606:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04607:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04608:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04609:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04610:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04611:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04612:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04613:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04614:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04615:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04616:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04617:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04618:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04619:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04620:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04621:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04622:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04623:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04624:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04625:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04626:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04627:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04628:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04629:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04630:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04631:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04632:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04633:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04634:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04635:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04636:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04637:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04638:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04639:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04640:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04641:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04642:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04643:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04644:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04645:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04646:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04647:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04648:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04649:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04650:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04651:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04652:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04653:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04654:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04655:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04656:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04657:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04658:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04659:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04660:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04661:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04662:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04663:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04664:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04665:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04666:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04667:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04668:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04669:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04670:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04671:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04672:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04673:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04674:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04675:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04676:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04677:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04678:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04679:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04680:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04681:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04682:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04683:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04684:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04685:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04686:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04687:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04688:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04689:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04690:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04691:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04692:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04693:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04694:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04695:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04696:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04697:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04698:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04699:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04700:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04701:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04702:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04703:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04704:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04705:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04706:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04707:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04708:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04709:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04710:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04711:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04712:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04713:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04714:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04715:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04716:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04717:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04718:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04719:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04720:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04721:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04722:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04723:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04724:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04725:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04726:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04727:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04728:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04729:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04730:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04731:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04732:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04733:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04734:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04735:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04736:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04737:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04738:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04739:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04740:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04741:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04742:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04743:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04744:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04745:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04746:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04747:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04748:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04749:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04750:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04751:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04752:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04753:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04754:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04755:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04756:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04757:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04758:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04759:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04760:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04761:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04762:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04763:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04764:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04765:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04766:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04767:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04768:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04769:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04770:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04771:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04772:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04773:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04774:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04775:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04776:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04777:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04778:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04779:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04780:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04781:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04782:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04783:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04784:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04785:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04786:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04787:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04788:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04789:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04790:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04791:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04792:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04793:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04794:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04795:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04796:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04797:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04798:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04799:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04800:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04801:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04802:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04803:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04804:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04805:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04806:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04807:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04808:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04809:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04810:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04811:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04812:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04813:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04814:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04815:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04816:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04817:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04818:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04819:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04820:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04821:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04822:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04823:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04824:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04825:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04826:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04827:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04828:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04829:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04830:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04831:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04832:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04833:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04834:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04835:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04836:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04837:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04838:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04839:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04840:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04841:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04842:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04843:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04844:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04845:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04846:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04847:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04848:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04849:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04850:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04851:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04852:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04853:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04854:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04855:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04856:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04857:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04858:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04859:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04860:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04861:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04862:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04863:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04864:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04865:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04866:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04867:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04868:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04869:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04870:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04871:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04872:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04873:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04874:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04875:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04876:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04877:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04878:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04879:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04880:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04881:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04882:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04883:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04884:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04885:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04886:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04887:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04888:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04889:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04890:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04891:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04892:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04893:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04894:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04895:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04896:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04897:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04898:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04899:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04900:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04901:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04902:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04903:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04904:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04905:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04906:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04907:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04908:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04909:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04910:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04911:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04912:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04913:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04914:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04915:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04916:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04917:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04918:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04919:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04920:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04921:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04922:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04923:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04924:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04925:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04926:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04927:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04928:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04929:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04930:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04931:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04932:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04933:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04934:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04935:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04936:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04937:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04938:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04939:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04940:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04941:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04942:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04943:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04944:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04945:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04946:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04947:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04948:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04949:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04950:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04951:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04952:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04953:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04954:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04955:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04956:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04957:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04958:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04959:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04960:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04961:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04962:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04963:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04964:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04965:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04966:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04967:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04968:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04969:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04970:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04971:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04972:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04973:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04974:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04975:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04976:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04977:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04978:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04979:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04980:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04981:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04982:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04983:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04984:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04985:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04986:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04987:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04988:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04989:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_addr_04990:
  shows
    "pmp_addr (pmp_encode_model addr pmp_sz perm s) = addr div 4"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_size_04991:
  shows
    "pmp_size (pmp_encode_model addr pmp_sz perm s) = pmp_sz"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_perm_04992:
  shows
    "pmp_perm (pmp_encode_model addr pmp_sz perm s) = perm"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_valid_04993:
  shows
    "pmp_valid (pmp_encode_model addr pmp_sz perm s) = (4 \<le> pmp_sz)"
  by (simp add: pmp_encode_model_def)

lemma SeSBI_PMP_Frame_cfg_04994:
  shows
    "pmp_cfg_index (pmp_encode_model addr pmp_sz perm s) = pmp_cfg_index s"
  by (simp add: pmp_encode_model_def)

lemmas SeSBI_PMP_Frame_anchor_00000 = refl
end
