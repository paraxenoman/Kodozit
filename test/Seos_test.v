Require Import Kodozit.Seos.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import ExtLib.Structures.Monad.
Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.

(* Тривиальный пример хорошей программы *)
Example example_good_prog0 := [
  SC_DeclVar "minprod" (SE_Prod [SE_Elem "bla"; SE_Unit]); 
  SC_DeclVar "myvar" (SE_Prod [SE_TRep (ST_Elem "one"); SE_Elem "0"; SE_Elem "2"; SE_Var "minprod"]);
  SC_Eval (SE_Prod [SE_App (SE_Var "myvar") (SE_Prim Prm_Left); SE_App (SE_Var "myvar") (SE_Prim Prm_Right)]) ].
Compute (run_prog example_good_prog0).

(* Хорошая программа -  объявление типов-комбинаций *)
Example example_good_prog2 := [
  SC_DeclCombVariant "Bool" (ST_Elem "true") [] [];
  SC_DeclCombVariant "Bool" (ST_Elem "false") [] [];
  SC_CloseCombType "Bool";
  SC_Eval (SE_Comb (SE_Elem "true") [])
].
Compute (run_prog example_good_prog2).

(* Хорошая программа -  объявление индуктивного типа натуральных чисел *)
Example example_good_prog3 := [
  SC_DeclCombVariant "Option" (ST_Elem "None") ["a"] [ST_TRep (ST_Hole "a")];
  SC_DeclCombVariant "Option" (ST_Elem "Some") ["a"] [ST_Hole "a"];
  SC_CloseCombType "Option";
  SC_DeclCombVariant "Nat" (ST_Elem "Zero") [] [];
  SC_DeclCombVariant "Nat" (ST_Elem "Succ") [] [ST_Comb "Nat" []];
  SC_CloseCombType "Nat";
  SC_DeclVar "zero" (SE_Comb (SE_Elem "Zero") []);
  SC_Eval (SE_Comb (SE_Elem "Some") [SE_Comb (SE_Elem "Succ") [SE_Var "zero"]])
].
Compute (run_prog example_good_prog3).

(* Хорошая программа - типы комбинаций с параметрами произвольных типов *)
Example example_good_prog4 := [
  SC_DeclCombVariant "Foo" (ST_Elem "Foo") ["a"; "b"] [ST_Hole "a"; ST_Hole "b"];
  SC_CloseCombType "Foo";
  SC_Eval (SE_Comb (SE_Elem "Foo") [SE_Unit; (SE_Prim Prm_Left)])
].
Compute (run_prog example_good_prog4).

(* Хорошая программа - типы комбинаций с параметрами одинаковых типов *)
Example example_good_prog5 := [
  SC_DeclCombVariant "Foo" (ST_Elem "Foo") ["a"] [ST_Hole "a"; ST_Hole "a"];
  SC_CloseCombType "Foo";
  SC_Eval (SE_Comb (SE_Elem "Foo") [SE_Unit; SE_Unit])
].
Compute (run_prog example_good_prog5).

(* Хорошая программа -  применение SE_Prim к комбинации *)
Example example_good_prog6 := [
  SC_DeclCombVariant "Option" (ST_Elem "None") ["a"] [ST_TRep (ST_Hole "a")];
  SC_DeclCombVariant "Option" (ST_Elem "Some") ["a"] [ST_Hole "a"];
  SC_CloseCombType "Option";
  SC_DeclCombVariant "Nat" (ST_Elem "Zero") [] [];
  SC_DeclCombVariant "Nat" (ST_Elem "Succ") [] [ST_Comb "Nat" []];
  SC_CloseCombType "Nat";
  SC_DeclVar "zero" (SE_Comb (SE_Elem "Zero") []);
  SC_DeclVar "comb" (SE_Comb (SE_Elem "Some") [SE_Comb (SE_Elem "Succ") [SE_Var "zero"]]);
  SC_Eval (SE_App (SE_Var "comb") (SE_Prim Prm_Right))
].
Compute (run_prog example_good_prog6).

(* Хорошая программа - Тип списков *)
Example example_good_prog7 := [
  SC_DeclCombVariant "Nat" (ST_Elem "Zero") [] [];
  SC_DeclCombVariant "Nat" (ST_Elem "Succ") [] [ST_Comb "Nat" []];
  SC_CloseCombType "Nat";
  SC_DeclCombVariant "List" (ST_Elem "Nil") ["a"] [ST_TRep (ST_Hole "a")];
  SC_DeclCombVariant "List" (ST_Elem "Cons") ["a"] [ST_Hole "a"; ST_Comb "List" [ST_Hole "a"]];
  SC_CloseCombType "List";
  SC_DeclVar "zero" (SE_Comb (SE_Elem "Zero") []);
  SC_Eval (SE_Comb (SE_Elem "Cons") [
      SE_Var "zero"; 
      (SE_Comb (SE_Elem "Nil") [SE_TRep (ST_Comb "Nat" [])])
  ])
].
Compute (run_prog example_good_prog7).

(* Плохая программа - несоблюдение ограничений типов *)
Example example_bad_prog0 := [
  SC_DeclCombVariant "Foo" (ST_Elem "Foo") [] [ST_Hole "a"; ST_Hole "a"];
  SC_CloseCombType "Foo";
  SC_Eval (SE_Comb (SE_Elem "Foo") [SE_Unit; SE_Elem "bla"])
].
Compute (run_prog example_bad_prog0).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog1 := [
  SC_DeclVar "bed" (SE_Elem "()"); 
  SC_Eval (SE_Var "bad")].
Compute (run_prog example_bad_prog1).

(* Плохая программа - затенение переменных *)
Example example_bad_prog2 := [
  SC_DeclVar "input" (SE_Elem "bla");
  SC_DeclVar "input" (SE_Prod [SE_Elem "0"; SE_Elem "2"; SE_Elem "VAL"])
].
Compute (run_prog example_bad_prog2).

(* Плохая программа - объявление типов и их синонимов с занятыми именами *)
Example example_bad_prog3 := [
  SC_NewTypeAbbr "NatZero" (ST_Elem "Nat");
  SC_DeclCombVariant "NatZero" (ST_Prod [ST_Elem "Zero"; (ST_Prod [ST_Elem "Nat"])]) [] []
].
Compute (run_prog example_bad_prog3).

(* Плохая программа - объявление типов комбинаций с одинаковым конструктором данных *)
Example example_bad_prog4 := [
  SC_NewTypeAbbr "TP" (ST_Prod [ST_Elem "Zero"; ST_Elem "Nat"]);
  SC_DeclCombVariant "NatZero" (ST_Prod [ST_Elem "Zero"; ST_Elem "Nat"]) [] [];
  SC_DeclCombVariant "NatZeroCopy" (ST_Abbr "TP") [] []
].
Compute (run_prog example_bad_prog4).

(* Плохая программа - попытка расширить закрытый тип *)
Example example_bad_prog5 := [
  SC_DeclCombVariant "Bool" (ST_Elem "true") [] [];
  SC_DeclCombVariant "Bool" (ST_Elem "false") [] [];
  SC_CloseCombType "Bool";
  SC_DeclCombVariant "Bool" (ST_Elem "undef") [] [];
  SC_Eval (SE_Comb (SE_Elem "false") [])
].
Compute (run_prog example_bad_prog5).

(* Плохая программа - попытка использовать ST_Prim в конструкторе данных для типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog6 := [
  SC_DeclCombVariant "Bar" (ST_Prod [ST_Elem "a"; ST_Prim Prm_Left]) [] []
].
Compute (run_prog example_bad_prog6).

(* Плохая программа - попытка использовать ST_Prim в параметрах типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog7 := [
  SC_DeclCombVariant "Bar" (ST_Elem "a") [] [ST_Prod [ST_Prim Prm_Left; ST_Elem "x"]]
].
Compute (run_prog example_bad_prog7).

(* Плохая программа - ошибочное применение Prm_Left *)
Example example_good_prog8 : run_prog [
    SC_DeclVar "myvar" (SE_Prod []);
    SC_Eval (SE_App (SE_Var "myvar") (SE_Prim Prm_Left))
  ]
  = Err (TypeErr_InvalidApp NT_Unit (NT_Prim Prm_Left)).
Proof.
  reflexivity.
Qed.

(* Плохая программа - закрытие несуществующего типа *)
Example example_good_prog9 : run_prog [
  SC_CloseCombType "Bool"
] 
= Err (TypeErr_CloseUnknownComb "Bool").
Proof.
  reflexivity.
Qed.

(* Плохая программа - повторное закрытие типа *)
Example example_good_prog10 : 
  run_prog [
    SC_DeclCombVariant "Bool" (ST_Elem "true") [] [];
    SC_DeclCombVariant "Bool" (ST_Elem "false") [] [];
    SC_CloseCombType "Bool";
    SC_CloseCombType "Bool"
  ]
  = 
  Err (TypeErr_CombAlreadyClosed "Bool").
Proof.
  reflexivity.
Qed.

Example invalid_prod_with_one_member : 
  run_prog [
    SC_Eval (SE_Prod [SE_Elem ""])
  ] 
  =
  Err (ExprErr_InvalidProd (CE_Prod [CE_Elem ""])).
Proof.
  reflexivity.
Qed.

Example norm_type_beq_unit :
  norm_type_beq NT_Unit NT_Unit = true.
Proof.
  reflexivity.
Qed.

Example norm_type_beq_prod :
  norm_type_beq
    (NT_Prod
      (NT_Elem "a")
      (NT_Elem "b")
      [])
    (NT_Prod
      (NT_Elem "a")
      (NT_Elem "b")
      [])
  = true.
Proof.
  reflexivity.
Qed.

Example norm_type_beq_prod_order :
  norm_type_beq
    (NT_Prod
      (NT_Elem "a")
      (NT_Elem "b")
      [])
    (NT_Prod
      (NT_Elem "b")
      (NT_Elem "a")
      [])
  = false.
Proof.
  reflexivity.
Qed.

Example normal_type_hole_detected :
  norm_type_contains_hole
    (NT_Comb "Box" [NT_Hole "A"])
  = true.
Proof.
  reflexivity.
Qed.

Example normal_type_without_holes :
  norm_type_contains_hole
    (NT_Prod
      (NT_Elem "a")
      (NT_Elem "b")
      [])
  = false.
Proof.
  reflexivity.
Qed.

Example duplicate_normal_map_key :
  find_duplicate_map_key
    []
    [(NT_Unit, NT_Elem "v1");
     (NT_Unit, NT_Elem "v2")]
  =
  Some NT_Unit.
Proof.
  reflexivity.
Qed.

Example unify_normal_hole :
  unify_norm_type
    []
    (NT_Hole "X")
    (NT_Elem "value")
  =
  Ok [("X", NT_Elem "value")].
Proof.
  reflexivity.
Qed.

Example unify_normal_bound_hole :
  unify_norm_type
    [("X", NT_Elem "value")]
    (NT_Hole "X")
    (NT_Elem "value")
  =
  Ok [("X", NT_Elem "value")].
Proof.
  reflexivity.
Qed.

Example unify_normal_bound_hole_mismatch :
  unify_norm_type
    [("X", NT_Elem "first")]
    (NT_Hole "X")
    (NT_Elem "second")
  =
  Err
    (TypeErr_Mismatch
      (NT_Elem "first")
      (NT_Elem "second")).
Proof.
  reflexivity.
Qed.

Example unify_rejects_hole_in_actual :
  unify_norm_type
    []
    (NT_Hole "X")
    (NT_Comb "Box" [NT_Hole "Y"])
  =
  Err
    (TypeErr_UseHole
      (NT_Comb "Box" [NT_Hole "Y"])).
Proof.
  reflexivity.
Qed.

Example unify_normal_products :
  unify_norm_type
    []
    (NT_Prod
      (NT_Hole "X")
      (NT_Elem "b")
      [])
    (NT_Prod
      (NT_Elem "a")
      (NT_Elem "b")
      [])
  =
  Ok [("X", NT_Elem "a")].
Proof.
  reflexivity.
Qed.

Example unify_normal_comb_argument_count_mismatch :
  unify_norm_type
    []
    (NT_Comb
      "Pair"
      [NT_Hole "A";
       NT_Hole "B"])
    (NT_Comb
      "Pair"
      [NT_Elem "a"])
  =
  Err
    (TypeErr_ListMismatch
      [NT_Hole "A"; NT_Hole "B"]
      [NT_Elem "a"]).
Proof.
  reflexivity.
Qed.

Example unify_normal_map_permutation :
  unify_norm_type
    []
    (NT_Map
      [(NT_Elem "k1", NT_Hole "X");
       (NT_Elem "k2", NT_Hole "Y")])
    (NT_Map
      [(NT_Elem "k2", NT_Elem "v2");
       (NT_Elem "k1", NT_Elem "v1")])
  =
  Ok
    [("Y", NT_Elem "v2");
     ("X", NT_Elem "v1")].
Proof.
  reflexivity.
Qed.

Definition elaborate_prog (prg : source_prog) : result core_prog :=
  let fix elaborate_commands
      (est : elaboration_state)
      (cmds : source_prog)
      {struct cmds}
      : result core_prog :=
      match cmds with
      | [] => Ok []
      | cmd :: rest =>
          ec <- elaborate_command est cmd ;;
          rest' <-
            elaborate_commands
              (ec_elaboration_state ec)
              rest ;;
          match ec_core_command ec with
          | None => Ok rest'
          | Some core_cmd => Ok (core_cmd :: rest')
          end
      end
  in
  elaborate_commands initial_elaboration_state prg.

Example elaborate_recursive_comb_type :
  elaborate_prog
    [
      SC_DeclCombVariant
        "List"
        (ST_Elem "Nil")
        ["A"]
        [];

      SC_DeclCombVariant
        "List"
        (ST_Elem "Cons")
        ["A"]
        [
          ST_Hole "A";
          ST_Comb "List" [ST_Hole "A"]
        ];

      SC_CloseCombType "List"
    ]
  =
  Ok
    [
      CC_DeclCombVariant
        "List"
        (CT_Elem "Nil")
        ["A"]
        [];

      CC_DeclCombVariant
        "List"
        (CT_Elem "Cons")
        ["A"]
        [
          CT_Hole "A";
          CT_Comb "List" [CT_Hole "A"]
        ];

      CC_CloseCombType "List"
    ].
Proof.
  reflexivity.
Qed.

Example elaborate_first_recursive_variant :
  elaborate_prog
    [
      SC_DeclCombVariant
        "Stream"
        (ST_Elem "Cons")
        ["A"]
        [
          ST_Hole "A";
          ST_Comb "Stream" [ST_Hole "A"]
        ];

      SC_CloseCombType "Stream"
    ]
  =
  Ok
    [
      CC_DeclCombVariant
        "Stream"
        (CT_Elem "Cons")
        ["A"]
        [
          CT_Hole "A";
          CT_Comb "Stream" [CT_Hole "A"]
        ];

      CC_CloseCombType "Stream"
    ].
Proof.
  reflexivity.
Qed.


Example elaborate_allows_multiple_comb_variants :
  elaborate_prog
    [
      SC_DeclCombVariant
        "Choice"
        (ST_Elem "left")
        []
        [];

      SC_DeclCombVariant
        "Choice"
        (ST_Elem "right")
        []
        []
    ]
  =
  Ok
    [
      CC_DeclCombVariant
        "Choice"
        (CT_Elem "left")
        []
        [];

      CC_DeclCombVariant
        "Choice"
        (CT_Elem "right")
        []
        []
    ].
Proof.
  reflexivity.
Qed.


Example elaborate_removes_transitive_type_abbrs :
  elaborate_prog
    [
      SC_NewTypeAbbr
        "A"
        (ST_Elem "x");

      SC_NewTypeAbbr
        "B"
        (ST_Abbr "A");

      SC_NewTypeAbbr
        "C"
        (ST_Prod
           [ST_Abbr "B";
            ST_Elem "y"]);

      SC_Eval
        (SE_TRep (ST_Abbr "C"))
    ]
  =
  Ok
    [
      CC_Eval
        (CE_TRep
           (CT_Prod
              [CT_Elem "x";
               CT_Elem "y"]))
    ].
Proof.
  reflexivity.
Qed.

Example elaborate_removes_type_abbr_command :
  elaborate_prog
    [
      SC_NewTypeAbbr
        "A"
        (ST_Elem "x");

      SC_Eval
        (SE_TRep (ST_Abbr "A"))
    ]
  =
  Ok
    [
      CC_Eval
        (CE_TRep (CT_Elem "x"))
    ].
Proof.
  reflexivity.
Qed.

Example elaborate_rejects_abbr_then_comb_same_name :
  elaborate_prog
    [
      SC_NewTypeAbbr
        "T"
        (ST_Elem "x");

      SC_DeclCombVariant
        "T"
        (ST_Elem "ctor")
        []
        []
    ]
  =
  Err (TypeErr_DuplicateType "T").
Proof.
  reflexivity.
Qed.

Example elaborate_rejects_comb_then_abbr_same_name :
  elaborate_prog
    [
      SC_DeclCombVariant
        "T"
        (ST_Elem "ctor")
        []
        [];

      SC_NewTypeAbbr
        "T"
        (ST_Elem "x")
    ]
  =
  Err (TypeErr_DuplicateType "T").
Proof.
  reflexivity.
Qed.

Example elaborate_rejects_duplicate_abbr :
  elaborate_prog
    [
      SC_NewTypeAbbr
        "T"
        (ST_Elem "x");

      SC_NewTypeAbbr
        "T"
        (ST_Elem "y")
    ]
  =
  Err (TypeErr_DuplicateType "T").
Proof.
  reflexivity.
Qed.

Example elaborate_rejects_unknown_abbr :
  elaborate_prog
    [
      SC_Eval
        (SE_TRep (ST_Abbr "Unknown"))
    ]
  =
  Err (Err_UnboundTypeAbbr "Unknown").
Proof.
  reflexivity.
Qed.

Example elaborated_program_contains_no_abbr :
    elaborate_prog
      [
        SC_NewTypeAbbr
          "A"
          (ST_Elem "x");

        SC_NewTypeAbbr
          "B"
          (ST_Prod
             [ST_Abbr "A";
              ST_Elem "y"]);

        SC_Eval
          (SE_TRep (ST_Abbr "B"))
      ]
  =
  Ok [CC_Eval (CE_TRep (CT_Prod [CT_Elem "x"; CT_Elem "y"]))].
Proof.
  reflexivity.
Qed.

Example elaborate_unknown_type_abbr :
  elaborate_prog
    [
      SC_Eval
        (SE_TRep (ST_Abbr "Unknown"))
    ]
  =
  Err (Err_UnboundTypeAbbr "Unknown").
Proof.
  reflexivity.
Qed.

Example elaborate_forward_type_reference :
  elaborate_prog
    [
      SC_Eval
        (SE_TRep (ST_Abbr "A"));

      SC_NewTypeAbbr
        "A"
        (ST_Elem "x")
    ]
  =
  Err (Err_UnboundTypeAbbr "A").
Proof.
  reflexivity.
Qed.


Example elaborate_abbr_inside_map :
  elaborate_prog
    [
      SC_NewTypeAbbr
        "Key"
        (ST_Elem "key");

      SC_NewTypeAbbr
        "Value"
        (ST_Elem "value");

      SC_Eval
        (SE_TRep
           (ST_Map
              [(ST_Abbr "Key",
                ST_Abbr "Value")]))
    ]
  =
  Ok [CC_Eval (CE_TRep (CT_Map [(CT_Elem "key", CT_Elem "value")]))].
Proof.
  reflexivity.
Qed.

Example self_abbr_is_unbound :
  elaborate_prog
    [SC_NewTypeAbbr "A" (ST_Abbr "A")]
  =
    Err (Err_UnboundTypeAbbr "A").
Proof.
  reflexivity.
Qed.

Example forward_abbr_is_unbound :
  elaborate_prog
    [SC_NewTypeAbbr "A" (ST_Abbr "B"); SC_NewTypeAbbr "B" (ST_Abbr "A")]
  =
    Err (Err_UnboundTypeAbbr "B").
Proof.
  reflexivity.
Qed.

Example unify_map_empty :
  unify_norm_type []
    (NT_Map [])
    (NT_Map []) =
  Ok [].
Proof.
  reflexivity.
Qed.

Example unify_empty_map_pattern :
  unify_norm_type []
    (NT_Map [])
    (NT_Map
       [(NT_Elem "key1", NT_Elem "value1");
        (NT_Elem "key2", NT_Elem "value2")]) =
  Ok [].
Proof.
  reflexivity.
Qed.

Example valid_map_pattern_ok :
  validate_map_pattern_keys
    (NT_Map
       [(NT_Elem "key1", NT_Hole "V1");
        (NT_Elem "key2", NT_Hole "V2")]) =
  Ok tt.
Proof.
  reflexivity.
Qed.

Example invalid_duplicate_map_pattern_key :
  validate_map_pattern_keys
    (NT_Map
       [(NT_Elem "key", NT_Hole "V1");
        (NT_Elem "key", NT_Hole "V2")]) =
  Err
    (TypeErr_DuplicateMapPatternKey
       (NT_Elem "key")).
Proof.
  reflexivity.
Qed.

Example invalid_hole_in_map_pattern_key :
  validate_map_pattern_keys
    (NT_Map
       [(NT_Hole "K", NT_Hole "V")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (NT_Hole "K")).
Proof.
  reflexivity.
Qed.

Example invalid_nested_duplicate_map_pattern_key :
  validate_map_pattern_keys
    (NT_Map
       [(NT_Elem "outer",
         NT_Map
           [(NT_Elem "inner", NT_Hole "V1");
            (NT_Elem "inner", NT_Hole "V2")])]) =
  Err
    (TypeErr_DuplicateMapPatternKey
       (NT_Elem "inner")).
Proof.
  reflexivity.
Qed.

Example unify_map_rejects_hole_in_key :
  unify_norm_type []
    (NT_Map
       [(NT_Hole "K", NT_Hole "V")])
    (NT_Map
       [(NT_Elem "key", NT_Elem "value");
        (NT_Elem "key2", NT_Elem "val")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (NT_Hole "K")).
Proof.
  reflexivity.
Qed.

Example unify_map_rejects_nested_hole_in_key :
  unify_norm_type []
    (NT_Map
       [(NT_Prod (NT_Elem "prefix") (NT_Hole "K") [],
         NT_Hole "V")])
    (NT_Map
       [(NT_Prod (NT_Elem "prefix") (NT_Elem "key") [],
         NT_Elem "value")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (NT_Prod (NT_Elem "prefix") (NT_Hole "K") [])).
Proof.
  reflexivity.
Qed.

Example unify_map_permuted :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "key1", NT_Hole "V1");
        (NT_Elem "key2", NT_Hole "V2")])
    (NT_Map
       [(NT_Elem "key2", NT_Prim Prm_Right);
        (NT_Elem "key3", NT_Elem "unused");
        (NT_Elem "key1", NT_Prim Prm_Left)]) =
  Ok
    [("V2", NT_Prim Prm_Right);
     ("V1", NT_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_concrete_key :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "key", NT_Hole "V")])
    (NT_Map
       [(NT_Elem "key", NT_Elem "value");
        (NT_Elem "key2", NT_Elem "val")]) =
  Ok
    [("V", NT_Elem "value")].
Proof.
  reflexivity.
Qed.

Example unify_map_shared_value_hole :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "key1", NT_Hole "V");
        (NT_Elem "key2", NT_Hole "V")])
    (NT_Map
       [(NT_Elem "key2", NT_Prim Prm_Left);
        (NT_Elem "key1", NT_Prim Prm_Left)]) =
  Ok
    [("V", NT_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_different_lengths :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "a", NT_Hole "X")])
    (NT_Map
       [(NT_Elem "a", NT_Prim Prm_Left);
        (NT_Elem "b", NT_Prim Prm_Right)]) =
  Ok [("X", NT_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_inconsistent_value_hole :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "key1", NT_Hole "V");
        (NT_Elem "key2", NT_Hole "V")])
    (NT_Map
       [(NT_Elem "key1", NT_Prim Prm_Left);
        (NT_Elem "key2", NT_Prim Prm_Right)]) =
  Err
    (TypeErr_Mismatch
       (NT_Prim Prm_Left)
       (NT_Prim Prm_Right)).
Proof.
  reflexivity.
Qed.

Example unify_map_missing_key :
  unify_norm_type []
    (NT_Map
       [(NT_Elem "missing", NT_Hole "V")])
    (NT_Map
       [(NT_Elem "key", NT_Elem "value")]) =
  Err
    (TypeErr_Mismatch
       (NT_Map
          [(NT_Elem "missing", NT_Hole "V")])
       (NT_Map
          [(NT_Elem "key", NT_Elem "value")])).
Proof.
  reflexivity.
Qed.

Example core_type_beq_map_permutation :
  norm_type_beq
    (NT_Map
       [(NT_Elem "K1", NT_Elem "V1");
        (NT_Elem "K2", NT_Elem "V2")])
    (NT_Map
       [(NT_Elem "K2", NT_Elem "V2");
        (NT_Elem "K1", NT_Elem "V1")])
  = true.
Proof.
  reflexivity.
Qed.

Example core_type_beq_map_different_values :
  norm_type_beq
    (NT_Map
       [(NT_Elem "K1", NT_Elem "V1");
        (NT_Elem "K2", NT_Elem "V2")])
    (NT_Map
       [(NT_Elem "K2", NT_Elem "X");
        (NT_Elem "K1", NT_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example core_type_beq_map_different_lengths :
  norm_type_beq
    (NT_Map
       [(NT_Elem "K1", NT_Elem "V1")])
    (NT_Map
       [(NT_Elem "K1", NT_Elem "V1");
        (NT_Elem "K2", NT_Elem "V2")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_permutation :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K2", V_Elem "V2");
        (V_Elem "K1", V_Elem "V1")])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_same_keys_different_values :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K2", V_Elem "X");
        (V_Elem "K1", V_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_different_keys :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K3", V_Elem "V2");
        (V_Elem "K1", V_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_different_lengths :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1")])
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_nested_permutation :
  value_beq
    (V_Map
       [(V_Elem "outer",
         V_Map
           [(V_Elem "K1", V_Elem "V1");
            (V_Elem "K2", V_Elem "V2")])])
    (V_Map
       [(V_Elem "outer",
         V_Map
           [(V_Elem "K2", V_Elem "V2");
            (V_Elem "K1", V_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_entry_permutation_and_nested_permutation :
  value_beq
    (V_Map
       [(V_Elem "A",
         V_Map
           [(V_Elem "K1", V_Elem "V1");
            (V_Elem "K2", V_Elem "V2")]);
        (V_Elem "B", V_Elem "VB")])
    (V_Map
       [(V_Elem "B", V_Elem "VB");
        (V_Elem "A",
         V_Map
           [(V_Elem "K2", V_Elem "V2");
            (V_Elem "K1", V_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_duplicate_multiplicity_equal :
  value_beq
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V");
        (V_Elem "X", V_Elem "Y")])
    (V_Map
       [(V_Elem "X", V_Elem "Y");
        (V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V")])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_duplicate_multiplicity_different :
  value_beq
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V")])
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "X", V_Elem "Y")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_trep_map_permutation :
  value_beq
    (V_TRep
       (NT_Map
          [(NT_Elem "K1", NT_Elem "V1");
           (NT_Elem "K2", NT_Elem "V2")]))
    (V_TRep
       (NT_Map
          [(NT_Elem "K2", NT_Elem "V2");
           (NT_Elem "K1", NT_Elem "V1")]))
  = true.
Proof.
  reflexivity.
Qed.


Example infer_map_duplicate_key_test :
  infer_type_core_expr
    []
    (CE_Map
       [(CE_Elem "a", CE_Elem "1");
        (CE_Elem "a", CE_Elem "2")])
  =
  Err (TypeErr_DuplicateMapKey (NT_Elem "a")).
Proof.
  reflexivity.
Qed.

Example eval_map_duplicate_key_test :
  eval_core_expr
    (CE_Map
       [(CE_Elem "a", CE_Elem "1");
        (CE_Elem "a", CE_Elem "2")])
  =
  Err (ExprErr_DuplicateMapKey (CE_Elem "a")).
Proof.
  reflexivity.
Qed.

Example map_expr : core_expr :=
  CE_Map
    [(CE_Elem "a", CE_Elem "1");
     (CE_Elem "b", CE_Prod [CE_Elem "x"; CE_Elem "y"])].

Example infer_map_expr_test :
  infer_type_core_expr [] map_expr =
  Ok
    (NT_Map
       [(NT_Elem "a", NT_Elem "1");
        (NT_Elem "b",
         NT_Prod (NT_Elem "x") (NT_Elem "y") [])]).
Proof.
  reflexivity.
Qed.

Example eval_map_expr_test :
  eval_core_expr map_expr =
  Ok
    (V_Map
       [(V_Elem "a", V_Elem "1");
        (V_Elem "b",
         V_Prod [V_Elem "x"; V_Elem "y"])]).
Proof.
  reflexivity.
Qed.

Example unify_generic_list
    (plst arglst : list norm_type)
  : result (list norm_type) :=
  match unify_norm_type_list [] plst arglst with
  | Ok _ => Ok arglst
  | Err e => Err e
  end.

Example test_unify_nested_prod :
  unify_generic_list
    [NT_Prod (NT_Hole "a") (NT_Elem "x") [] ]
    [NT_Prod (NT_Elem "Nat") (NT_Elem "x") [] ]
  =
  Ok [
    NT_Prod (NT_Elem "Nat") (NT_Elem "x") []
  ].
Proof.
  reflexivity.
Qed.

Example test_unify_repeated_nested_hole :
  unify_generic_list
    [
      NT_Hole "a";
      NT_Comb "Option" [NT_Hole "a"]
    ]
    [
      NT_Elem "Nat";
      NT_Comb "Option" [NT_Elem "Nat"]
    ]
  =
  Ok [
    NT_Elem "Nat";
    NT_Comb "Option" [NT_Elem "Nat"]
  ].
Proof.
  reflexivity.
Qed.

Example test_unify_repeated_nested_hole_error :
  unify_generic_list
    [
      NT_Hole "a";
      NT_Comb "Option" [NT_Hole "a"]
    ]
    [
      NT_Elem "Nat";
      NT_Comb "Option" [NT_Elem "Bool"]
    ]
  =
  Err
    (TypeErr_Mismatch
       (NT_Elem "Nat")
       (NT_Elem "Bool")).
Proof.
  reflexivity.
Qed.

Example test_unify_different_comb_names :
  unify_generic_list
    [NT_Comb "Option" [NT_Hole "a"]]
    [NT_Comb "List" [NT_Elem "Nat"]]
  =
  Err
    (TypeErr_Mismatch
       (NT_Comb "Option" [NT_Hole "a"])
       (NT_Comb "List" [NT_Elem "Nat"])).
Proof.
  reflexivity.
Qed.

Example test_unify_product_length_error :
  unify_generic_list
    [
      NT_Prod (NT_Hole "a") (NT_Hole "b") [NT_Hole "c"]
    ]
    [
      NT_Prod (NT_Elem "Nat") (NT_Elem "Nat2") []
    ]
  =
  Err
    (TypeErr_ListMismatch
       [NT_Hole "a"; NT_Hole "b"; NT_Hole "c"]
       [NT_Elem "Nat"; NT_Elem "Nat2"]).
Proof.
  reflexivity.
Qed.


