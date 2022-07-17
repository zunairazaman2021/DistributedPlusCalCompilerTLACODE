---- MODULE MC ----
EXTENDS GenProcessOnly, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_165529956742613000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Q
const_165529956742614000 == 
2
----

\* INIT definition @modelBehaviorNoSpec:0
init_165529956742615000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_165529956742616000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Jun 15 13:26:07 GMT 2022 by zunai
