theory test
  imports Main

begin

record 'a mmonoid =
  carrier :: "'a set"
  op :: "'a \<Rightarrow>( 'a \<Rightarrow> 'a)" (infixl \<open>\<otimes>\<index>\<close> 70)
  id :: 'a (\<open>\<one>\<index>\<close>)



(*Qual comando está fazendo o locale considerar o record mmonoid?*)
locale monoidasaasasa =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
      and m_assoc:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk>
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier G"
      and l_one [simp]: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
      and r_one [simp]: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"



end