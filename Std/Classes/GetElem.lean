/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

theorem getElem?_pos [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : Dom a i) [Decidable (Dom a i)] : a[i]? = a[i] := dif_pos h

theorem getElem?_neg [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : ¬Dom a i) [Decidable (Dom a i)] : a[i]? = none := dif_neg h
