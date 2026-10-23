# Actual compiled contract readout

Retrieved from independently rebuilt source via Lean Meta.ppExpr; no premise is added or removed. Exact types/body Expr bytes and producer occurrence evidence are retained separately.

## AllGoodDP.allGood_parts

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood T ss = true →
    ForestState.proper T ss = true ∧ ∀ (s : RMAF.Tree), s ∈ ss → ForestState.targetAgrees T s (RMAF.leaves s) = true
```

## AllGoodDP.actual_paint_spec

```lean
∀ (t : RMAF.Tree) (ss : List RMAF.Tree),
  ForestState.proper (some t) ss = true →
    AllGoodDP.Valid (List.range ss.length) (AllGoodDP.owner ss) t
        (AllGoodDP.solve (List.range ss.length) (AllGoodDP.owner ss) t) ∧
      ∀ (p : AllGoodDP.Paint),
        AllGoodDP.Valid (List.range ss.length) (AllGoodDP.owner ss) t p →
          AllGoodDP.changes (AllGoodDP.solve (List.range ss.length) (AllGoodDP.owner ss) t) ≤ AllGoodDP.changes p
```

## AllGoodDP.table_spec

```lean
∀ (cs : List Nat) (owner : Nat → Nat) (t : RMAF.Tree),
  cs ≠ [] →
    (∀ (x : Nat), x ∈ RMAF.leaves t → owner x ∈ cs) →
      AllGoodDP.table cs owner t ≠ [] ∧
        (∀ (p : AllGoodDP.Paint), p ∈ AllGoodDP.table cs owner t → AllGoodDP.Valid cs owner t p) ∧
          ∀ (p : AllGoodDP.Paint),
            AllGoodDP.Valid cs owner t p →
              ∃ b,
                b ∈ AllGoodDP.table cs owner t ∧
                  AllGoodDP.root b = AllGoodDP.root p ∧ AllGoodDP.changes b ≤ AllGoodDP.changes p
```

## AllGoodDP.solve_spec

```lean
∀ (cs : List Nat) (owner : Nat → Nat) (t : RMAF.Tree),
  cs ≠ [] →
    (∀ (x : Nat), x ∈ RMAF.leaves t → owner x ∈ cs) →
      AllGoodDP.Valid cs owner t (AllGoodDP.solve cs owner t) ∧
        ∀ (p : AllGoodDP.Paint),
          AllGoodDP.Valid cs owner t p → AllGoodDP.changes (AllGoodDP.solve cs owner t) ≤ AllGoodDP.changes p
```

## AllGoodDP.candidate_ownership

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  ForestState.proper T ss = true → ∀ (B : List Nat), B ∈ AllGoodDP.candidate T ss → ∃ s, s ∈ ss ∧ B ⊆ RMAF.leaves s
```

## AllGoodDP.allGood_completion

```lean
∀ (t : RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  ForestState.proper (some t) ss = true →
    (∀ (s : RMAF.Tree), s ∈ ss → ForestState.targetAgrees (some t) s (RMAF.leaves s) = true) →
      RMAF.partitionCheck (RMAF.leaves t) F = true →
        (∀ (B : List Nat), B ∈ F → ∃ s, s ∈ ss ∧ B ⊆ RMAF.leaves s) →
          RMAF.pairwiseEmbeddings t F = true → ForestState.agrees (some t) ss F = true
```

## AllGoodDP.candidate_agrees

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood T ss = true → ForestState.agrees T ss (AllGoodDP.candidate T ss) = true
```

## AllGoodDP.agreement_coloring

```lean
∀ (t : RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  ForestState.agrees (some t) ss F = true →
    ∃ p, AllGoodDP.Valid (List.range ss.length) (AllGoodDP.owner ss) t p ∧ AllGoodDP.changes p ≤ F.length - 1
```

## AllGoodDP.candidate_blocks_minimum

```lean
∀ (t : RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  ForestState.agrees (some t) ss F = true → (AllGoodDP.candidate (some t) ss).length ≤ F.length
```

## AllGoodDP.sources_le_blocks

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  ForestState.agrees T ss F = true → ss.length ≤ F.length
```

## AllGoodDP.additional_exact

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  ForestState.agrees T ss F = true → ForestState.additionalCost ss F + ss.length = F.length
```

## AllGoodDP.candidate_minimum

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood T ss = true →
    ForestState.agrees T ss (AllGoodDP.candidate T ss) = true ∧
      ∀ (F : List (List Nat)),
        ForestState.agrees T ss F = true →
          ForestState.additionalCost ss (AllGoodDP.candidate T ss) ≤ ForestState.additionalCost ss F
```

## AllGoodDP.candidate_no_leafless

```lean
∀ (t : RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood (some t) ss = true →
    ∀ (B : List Nat), B ∈ AllGoodDP.rawBlocks (AllGoodDP.solve (List.range ss.length) (AllGoodDP.owner ss) t) → B ≠ []
```

## AllGoodDP.run_sound

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree) (F : List (List Nat)),
  AllGoodDP.run T ss = some F → ForestState.agrees T ss F = true
```

## AllGoodDP.run_total_exact

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood T ss = true →
    ∃ F,
      AllGoodDP.run T ss = some F ∧
        ForestState.agrees T ss F = true ∧
          ForestState.additionalCost ss F + ss.length = F.length ∧
            ∀ (G : List (List Nat)),
              ForestState.agrees T ss G = true → ForestState.additionalCost ss F ≤ ForestState.additionalCost ss G
```

## AllGoodDP.decideBudget_correct

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree) (q : Nat),
  AllGoodDP.allGood T ss = true →
    (AllGoodDP.decideBudget T ss q = true ↔ ∃ F, ForestState.agrees T ss F = true ∧ ForestState.additionalCost ss F ≤ q)
```

## AllGoodDP.table_length

```lean
∀ (cs : List Nat) (owner : Nat → Nat) (t : RMAF.Tree),
  (AllGoodDP.table cs owner t).length =
    match t with
    | RMAF.Tree.leaf a => 1
    | a.node a_1 => cs.length
```

## AllGoodDP.visits_bound

```lean
∀ (r : Nat) (t : RMAF.Tree), AllGoodDP.visits r t ≤ AllGoodDP.vertices t * (r * (2 * (r + 1) + 1) + 1)
```

## AllGoodDPConsumerControls.literal_case_for_every_budget

```lean
∀ (T : Option RMAF.Tree) (ss : List RMAF.Tree),
  AllGoodDP.allGood T ss = true →
    ∃ F,
      AllGoodDP.run T ss = some F ∧
        ForestState.agrees T ss F = true ∧
          ForestState.additionalCost ss F + ss.length = F.length ∧
            ∀ (q : Nat),
              ForestState.additionalCost ss F ≤ q ↔
                ∃ G, ForestState.agrees T ss G = true ∧ ForestState.additionalCost ss G ≤ q
```
