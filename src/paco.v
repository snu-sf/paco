
Require Export paco0.
Require Export paco0_respectful.
Require Export paco1.
Require Export paco1_respectful.
Require Export paco2.
Require Export paco2_respectful.
Require Export paco3.
Require Export paco3_respectful.
Require Export paco4.
Require Export paco4_respectful.
Require Export paco5.
Require Export paco5_respectful.
Require Export paco6.
Require Export paco6_respectful.
Require Export paco7.
Require Export paco7_respectful.
Require Export paco8.
Require Export paco8_respectful.
Require Export paco9.
Require Export paco9_respectful.
Require Export paco10.
Require Export paco10_respectful.
Require Export paco11.
Require Export paco11_respectful.
Require Export paco12.
Require Export paco12_respectful.
Require Export paco13.
Require Export paco13_respectful.
Require Export paco14.
Require Export paco14_respectful.
Require Export paco15.
Require Export paco15_respectful.
Require Export paco16.
Require Export paco16_respectful.
Require Export paco17.
Require Export paco17_respectful.
Require Export paco18.
Require Export paco18_respectful.

Ltac pclearbot :=
  let X := fresh "_X" in
  repeat match goal with
         | [H: context[pacoid] |- _] =>
           first
             [red in H; destruct H as [H|X]; [|contradiction X]|(
                setoid_rewrite upaco0_clear in H ||
                setoid_rewrite upaco1_clear in H ||
                setoid_rewrite upaco2_clear in H ||
                setoid_rewrite upaco3_clear in H ||
                setoid_rewrite upaco4_clear in H ||
                setoid_rewrite upaco5_clear in H ||
                setoid_rewrite upaco6_clear in H ||
                setoid_rewrite upaco7_clear in H ||
                setoid_rewrite upaco8_clear in H ||
                setoid_rewrite upaco9_clear in H ||
                setoid_rewrite upaco10_clear in H ||
                setoid_rewrite upaco11_clear in H ||
                setoid_rewrite upaco12_clear in H ||
                setoid_rewrite upaco13_clear in H ||
                setoid_rewrite upaco14_clear in H ||
                setoid_rewrite upaco15_clear in H ||
                setoid_rewrite upaco16_clear in H ||
                setoid_rewrite upaco17_clear in H ||
                setoid_rewrite upaco18_clear in H ||
                fail)] end.
