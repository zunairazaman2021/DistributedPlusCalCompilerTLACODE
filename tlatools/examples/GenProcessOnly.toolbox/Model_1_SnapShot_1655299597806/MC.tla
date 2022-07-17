---- MODULE MC ----
EXTENDS GenProcessOnly, TLC

\* CONSTANT definitions @modelParameterConstants:0P
const_165529959472417000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Q
const_165529959472418000 == 
2
----

\* INIT definition @modelBehaviorNoSpec:0
init_165529959472419000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_165529959472420000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Jun 15 13:26:34 GMT 2022 by zunai
