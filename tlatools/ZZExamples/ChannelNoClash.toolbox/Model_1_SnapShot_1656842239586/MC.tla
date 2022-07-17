---- MODULE MC ----
EXTENDS ChannelNoClash, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_165684223652618000 == 
3
----

\* INIT definition @modelBehaviorNoSpec:0
init_165684223652619000 ==
FALSE/\ar = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_165684223652620000 ==
FALSE/\ar' = ar
----
=============================================================================
\* Modification History
\* Created Sun Jul 03 09:57:16 GMT 2022 by zunai
