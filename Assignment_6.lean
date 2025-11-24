import Mathlib
set_option linter.style.longLine false
set_option linter.style.commandStart false

------------------------------------------
-- LAB SIX: THE FINAL BOSS
------------------------------------------

-- This lab will require you to recall everything you learned over the course of the semester by way of Lean techniques (as well as how to define and manipulate logical syntax).

-- Define an inductive type called pform, which obeys the rules of syntax of propositional logic formulas. A pform can be an atomic formula (call this constructor at -- which takes as a parameter any string, of type String in Lean), or built using existing pform objects and the constructors myNot, myAnd, myOr, and myImp (standing for the usual operators). You must specify the fact that there is an algorithm to test for the syntactic equality of two pform objects.

-- Once you have defined this type, define an inductive object called pftree, which witnesses whether or not there is a proof of a pform φ from a finite set of pforms X (choose the type for this appropriately!) according to the rules given in Table 1 of https://www.cmi.ac.in/~spsuresh/pdfs/jlc2020-tr.pdf. This is a proof system in *intuitionistic* propositional logic, which means that it does not admit the law of excluded middle (i.e. φ ∨ ¬φ is not a tautology, and since this proof system is sound, cannot be proven without assumptions.) It also means, consequently, that anything proven must follow from the assumptions via a proof; there are no "free" axioms. Intuitionism has a long history, and goes back to Brouwer, and underpins much of theorem proving -- Lean's own underlying theory is intuitionistic.

-- In order to define a finite set, you will need to import Mathlib. Mathlib is THE Lean library, in that it includes a lot of handy constructs and tactics. In particular, it also includes the constructor called Finset, which takes as input a type, and spits out a finite set of said type (much like the List constructor). If you are using VSCode, if you type Finset followed by "." (exactly like with List) you can see the various methods and theorems you have access to under the Finset constructor. This is why we require the lines included above, which import the Mathlib library, and disable some irritating linters about line length and where a command should start.

-- Finally, define a theorem called mono_prf, which says that if there is a proof tree witnessing a proof of a pform φ from a Finset X of pforms, then there is a proof tree witnessing a proof of φ from a set which is a superset of X. Recall that you can state this in multiple ways; use whichever way seems most amenable to proving this statement. (This is what we have proved in class and called Monotonicity.) Submit your entire answer below this sequence of comments. In general, one wants to show not just Monotonicity, but various other desirable properties of any given proof system, including whether inference in them is decidable (and if it, how efficiently it can be done), like we are doing in that paper linked above.

inductive pform
    where
        | at : String → pform
        | myNot : pform → pform
        | myAnd : pform → pform → pform
        | myOr  : pform → pform → pform
        | myImp : pform → pform → pform

        deriving DecidableEq

inductive pftree : (Finset pform) → pform → Prop
    | ax ctx α :
        (pftree (insert α ctx) α)

    | not_i ctx α β :
        (pftree (insert α ctx) β) → (pftree (insert α ctx) (pform.myNot β)) → (pftree ctx (pform.myNot α))

    | not_e ctx α β:
        (pftree ctx β) → (pftree ctx (pform.myNot β)) → (pftree ctx α)

    | and_i ctx α β :
        (pftree ctx α) → (pftree ctx β) → (pftree ctx (pform.myAnd α β))

    | and_e_l ctx α_0 α_1 :
        (pftree ctx (pform.myAnd α_0 α_1)) → (pftree ctx α_0)

    | and_e_r ctx α_0 α_1 :
        (pftree ctx (pform.myAnd α_0 α_1)) → (pftree ctx α_1)

    | or_i_l ctx α_0 α_1:
        (pftree ctx α_0) → (pftree ctx (pform.myOr α_0 α_1))

    | or_i_r ctx α_0 α_1:
        (pftree ctx α_1) → (pftree ctx (pform.myOr α_0 α_1))

    | or_e ctx α β γ :
        (pftree ctx (pform.myOr α β)) → (pftree (insert α ctx) γ) → (pftree (insert β ctx) γ) → (pftree ctx γ)

    | imp_i ctx α β :
        (pftree (insert α ctx) β) → (pftree ctx (pform.myImp α β))

    | imp_p ctx α β :
        (pftree ctx β) → (pftree ctx (pform.myImp α β))

    | imp_e ctx α β :
        (pftree ctx (pform.myImp α β)) → (pftree ctx α) → (pftree ctx β)

theorem mono_prf :
    ∀ X : Finset pform, ∀ φ : pform,
    (pftree X φ) → ∀ s, X ⊆ s → (pftree s φ) :=

      by
        intro X φ h
        induction h with
          | ax ctx α =>
              intro s h_sub
              rw [← Finset.insert_erase (h_sub (Finset.mem_insert_self α ctx))]
              apply pftree.ax

          | not_i ctx α β h_not_i_1 h_not_i_2 ih1 ih2 =>
              intro s h_sub
              apply pftree.not_i
              · apply ih1
                exact Finset.insert_subset_insert α h_sub
              · apply ih2
                exact Finset.insert_subset_insert α h_sub

          | not_e ctx α β h_not_e_1 h_not_e_2 ih1 ih2 =>
              intro s h_sub
              apply pftree.not_e
              · apply ih1
                exact h_sub
              · apply ih2
                exact h_sub

          | and_i ctx α β h_and_i_1 h_and_i_2 ih1 ih2 =>
              intro s h_sub
              apply pftree.and_i
              · apply ih1
                exact h_sub
              · apply ih2
                exact h_sub

          | and_e_l ctx α_0 α_1 h_and_i ih =>
              intro s h_sub
              apply pftree.and_e_l
              apply ih
              exact h_sub

          | and_e_r ctx α_0 α_1 h_and_i ih =>
              intro s h_sub
              apply pftree.and_e_r
              apply ih
              exact h_sub

          | or_i_l ctx α_0 α_1 h_or_i ih =>
              intro s h_sub
              apply pftree.or_i_l
              apply ih
              exact h_sub

          | or_i_r ctx α_0 α_1 h_or_i ih =>
              intro s h_sub
              apply pftree.or_i_r
              apply ih
              exact h_sub

          | or_e ctx α β γ h_or_e_1 h_or_e_2 h_or_e_3 ih1 ih2 ih3 =>
              intro s h_sub
              apply pftree.or_e
              · apply ih1
                exact h_sub
              · apply ih2
                exact Finset.insert_subset_insert α h_sub
              apply ih3
              exact Finset.insert_subset_insert β h_sub

          | imp_i ctx α β h_imp_i ih =>
              intro s h_sub
              apply pftree.imp_i
              apply ih
              exact Finset.insert_subset_insert α h_sub

          | imp_p ctx α β h_imp_p ih =>
              intro s h_sub
              apply pftree.imp_p
              apply ih
              exact h_sub

          | imp_e ctx α β h_imp_p_1 h_imp_p_2 ih1 ih2 =>
              intro s h_sub
              apply pftree.imp_e
              · apply ih1
                exact h_sub
              · apply ih2
                exact h_sub
