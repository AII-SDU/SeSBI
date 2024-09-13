
datatype addr = Addr nat  (* 使用自然数模拟地址 *)
datatype size = Size nat  (* 同样用自然数模拟大小 *)
datatype prot = Prot nat  (* 保护标志的编码 *)
datatype result = Success | Error

definition valid_index :: "nat \<Rightarrow> bool" where
"valid_index idx \<longleftrightarrow> idx \<le> MAX_CSR_PMP"

definition log2roundup :: "size \<Rightarrow> nat" where
"log2roundup sz \<equiv> (LEAST n. 2^n \<ge> unSize sz)"  (* 计算向上取整的对数 *)

definition set_pmp :: "nat \<Rightarrow> addr \<Rightarrow> size \<Rightarrow> prot \<Rightarrow> result" where
"set_pmp idx start sz p \<equiv> 
  if \<not> valid_index idx \<or> log2roundup sz < PMP_SHIFT then Error
  else Success"
