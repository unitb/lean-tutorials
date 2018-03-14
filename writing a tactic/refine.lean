
import data.dlist

/- We want to write a set of tactics to automate the construction of
   instances. One approach might be to automate the specific instances
   that we are interested in. Instead, we will try to build reusable
   components and aim for wide applicability.

   Our first example of application is the construction of a `functor`
   instance for `(_ ⊕)`. We would like the instance to look like:

```
instance {α : Type*} : functor (sum α) :=
begin
  refineS { map := sum.map_right }, -- `refineS` focuses on structure fields
  field map_id
  { ... },
  field map_comp
  { ... },
end
```

   This structure is similar to the `cases / case id` syntax and we
   will use its underlying machinery to make our tactic work. We can
   identify two parts of the Lean API that we need to understand in
   order to make this work
     1. structure syntax and accessing field information
     2. using goal tagging

   Often, writing a new tactic involves using parts of the API that
   we're not fully familiar with so we're better get used to
   experimenting, making small prototypes to check if our
   understanding is correct. In the above example, we'd like to get
   the list of fields that are specified in the expression given to
   `refineS` and we'd like to know what are the fields that are
   missing in some sense. Let's start with the former.

   We set off to explore the core library and "grep" our way to useful
   functions:

```
library $ grep -R . -e structure
```

   The above is a miss: most of what we're getting is the list of
   structure declaration. What if we included underscores?

```
library $ grep -R . -e _structure
```

   It's a hit! We're getting
   https://github.com/leanprover/lean/blob/master/library/init/meta/pexpr.lean#L22-L31
   which looks promising. We reproduce the context below:

```
/-- Information about unelaborated structure instance expressions. -/
meta structure structure_instance_info :=
(struct       : option name := none)
(field_names  : list name)
(field_values : list pexpr)
(sources      : list pexpr := [])

/-- Create a structure instance expression. -/
meta constant pexpr.mk_structure_instance : structure_instance_info → pexpr
meta constant pexpr.get_structure_instance_info : pexpr → option structure_instance_info
```

Let's still try one more regex:

```
library $ grep -R . -e structure_
```

   We get more interesting stuff: https://github.com/leanprover/lean/blob/master/library/init/meta/environment.lean#L86-L87

```
/-- Return the fields of the structure with the given name, or `none` if it is not a structure -/
meta constant structure_fields : environment → name → option (list name)
```

   Let us see what `pexpr.get_structure_instance_info` tells us about `{ map := sum.map_right }`.
   We start by writing our tactic's type:
-/
open tactic

universes u v

example {α : Type u} : functor (sum α) :=
begin
  (do let e : pexpr := ``({ map := sum.map_right }),
      str ← e.get_structure_instance_info,
      trace str.field_names,
      trace str.field_values),
    -- prints:
    -- [map]
    -- [field_notation sum]
  admit
end

/- It's a success! It's important to see that `refineS₀` does no type
   checking on the expression we given it. This is why we get no error
   messages for `sum.map_right` not existing yet. `refineS₀`'s `e`
   argument is of type `parse texpr` which is definitionally equal to
   `pexpr`, the result of parsing an expression but doing no
   elaboration or type checking. In `parse texpr`, the type of `texpr`
   is `texpr : lean.parser pexpr` where `lean.parser` is the parsing
   monad.  Without going into details into `monads` as a programming
   construct or a mathematical object, objects of type `lean.parser α`
   are programs with access to the Lean parsing infrastructure
   including the current position of the parser and various parsing
   routines and the result of the program is of type `α`. Lean takes
   `parse texpr` as a hint that the tactic will be used interactively
   (as opposed to called by other tactics) and `texpr` is the parser
   to use to construct argument `e`. Other useful parsers can be found
   at https://github.com/leanprover/lean/blob/master/library/init/meta/interactive_base.lean#L69-L80.

   Our next experiment is to list the expected fields for the type
   that we are attempting to build. `environment.structure_fields`
   will help us in this:

```
meta constant structure_fields : environment → name → option (list name)
```

   What argument do we give it? Searching in `init/meta/tactic.lean`
   shows us that `get_env` will provide the first argument. The second
   argument is the type of the object that we're trying to build. More
   specifically, the name of that type.  If we call `target`, that
   type will be provided to us as an expression. In our case `functor
   (sum α)`. This expression contains multiple names. Which one do we
   want? Let us look at it closely by using `to_raw_fmt` to avoid any
   pretty printing and just get the syntax tree:

-/

example {α : Type u} : functor.{v} (sum α) :=
  -- (we use `.{v}` above so that Lean won't have to guess the universes which would
  -- create visual noise
begin
  (do let e : pexpr := ``({ map := sum.map_right }),
      tgt ← target,
      trace tgt.to_raw_fmt),
    -- prints:
    -- (app (const functor [v, max u v])
    --      (app (const sum [u, v])
    --           (local_const _ α (const 1 []))))
  admit
end

/- The printout shows us that our current type of interest is a
   function application whose function is `functor` and whose argument
   is another application. We don't actually care about any of the
   structure of the argument. The function is not always exactly what
   we care about either.  Consider for example `vector_space α β`. The
   function in the top-most application is `vector_space α` so we have
   to look at its function in order to land on `vector_space`
   itself. Does that mean that we have to look at the function of the
   function?  Let us consider a type class with the three arguments:
   `my_class α β γ`. The function of its function is `my_class α`. In
   short, we should keep retrieving functions until we run out of
   function applications. The result should be a constant and the name
   of that constant is what we need. If it is anything else than a
   constant, the user made a mistake and we will say no more of it
   here but various approaches can be taken for informative error
   messages.

   In `init/meta/expr.lean`, in the core library a function is
   provided to retrieve a function in a multi-argument function
   application: `expr.get_app_fn`.  It gives us another expression
   which we expect should be a constant. `expr.const_name` will reveal
   it's name.

-/
open nat
meta def mk_mvar_list : ℕ → tactic (list expr)
 | 0 := pure []
 | (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

open interactive interactive.types lean.parser
     tactic.interactive (itactic)

-- meta def tactic.interactive.refineS (e : parse texpr) : tactic unit :=
-- do    str ← e.get_structure_instance_info,
--       trace str.struct,
--       trace str.sources,
--       trace str.field_names,
--       tgt ← target,
--       let struct_n : name := tgt.get_app_fn.const_name,
--       env ← get_env,
--       exp_fields ← env.structure_fields struct_n,
--       let missing_f := (exp_fields.diff str.field_names).diff [`to_has_map],
--       vs ← mk_mvar_list missing_f.length,
--       let e' : pexpr := pexpr.mk_structure_instance
--           { -- struct := some struct_n
--           -- ,
--           field_names := str.field_names ++ missing_f
--           , field_values := str.field_values ++ vs.map to_pexpr },
--       refine ``(%%e' : %%tgt)

meta def var_names : expr → list name
 | (expr.pi n _ _ b) := n :: var_names b
 | _ := []

meta def drop_binders : expr → tactic expr
 | (expr.pi n bi t b) := b.instantiate_var <$> mk_local' n bi t >>= drop_binders
 | e := pure e

meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   [c] ← pure $ env.constructors_of struct_n | fail "too many constructors",
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

def dlist.join {α} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs

meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     e ← mk_const (n.update_prefix struct_n) >>= infer_type >>= drop_binders,
     expanded_field_list' $ e.get_app_fn.const_name),
   -- trace so, trace fs,
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)

meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

def mmap₂ {α β γ} {m : Type u → Type v} [applicative m] (f : α → β → m γ) : list α → list β → m (list γ)
 | [] _ := pure []
 | _ [] := pure []
 | (x :: xs) (y :: ys) := (::) <$> f x y <*> mmap₂ xs ys

def mmap₂' {α β γ} {m : Type u → Type v} [applicative m] (f : α → β → m γ) : list α → list β → m punit
 | [] _ := pure punit.star
 | _ [] := pure punit.star
 | (x :: xs) (y :: ys) := f x y *> mmap₂' xs ys

def sum.map_right {α β β'} (f : β → β') : α ⊕ β → α ⊕ β'
 | (sum.inr x) := sum.inr $ f x
 | (sum.inl x) := sum.inl x

meta def tactic.interactive.refineS (e : parse texpr) (ph : parse $ optional $ tk "with" *> ident) : tactic unit :=
do    str ← e.get_structure_instance_info,
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      exp_fields ← expanded_field_list struct_n,
      let exp_fields' := exp_fields.map prod.snd,
      let missing_f := exp_fields.filter (λ f, (f.2 : name) ∉ str.field_names),
      let provided := exp_fields.filter (λ f, (f.2 : name) ∈ str.field_names),
      vs ← mk_mvar_list missing_f.length,
      let e' : pexpr := pexpr.mk_structure_instance
          { struct := some struct_n
          , field_names := str.field_names ++ missing_f.map prod.snd
          , field_values := str.field_values ++ vs.map to_pexpr },
      refine e',
      gs ← with_enable_tags (
        mmap₂ (λ (n : name × name) v, do
           set_goals [v],
           try (interactive.unfold (provided.map $ λ ⟨s,f⟩, f.update_prefix s) (loc.ns [none])),
           apply_auto_param
             <|> apply_opt_param
             <|> (do match ph with
                       | (some ph) := () <$ (mk_const (n.2.update_prefix n.1) >>= pose ph none)
                       | none := return ()
                     end,
                     set_main_tag [`_field,n.2]),
           get_goals)
        missing_f vs),
      set_goals gs.join

meta def collect_tagged_goals (pre : name) : tactic (list expr) :=
do gs ← get_goals,
   gs.mfoldr (λ g r, do
      pre' :: t ← get_tag g,
      if t = [pre] ∧ pre' = pre'.get_prefix <.> "_field"
         then return (g::r)
         else return r)
      []

-- meta def match_field_tag

meta def tactic.interactive.field (tag : parse ident) (tac : itactic) : tactic unit :=
do ts ← collect_tagged_goals tag,
   match ts with
    | [] := fail format!"no field goal with tag {tag}"
    | [g] := do
      gs ← get_goals,
      set_goals $ g :: gs.filter (≠ g),
      solve1 tac
    | _ := fail format!"multiple goals have tag {tag}"
   end
universe w

instance {α : Type*} : functor (sum α) :=
  -- (we use `.{v}` above so that Lean won't have to guess the universes which would
  -- create visual noise
begin
  refineS { map := @sum.map_right _, .. } with law,
  all_goals { intros, casesm _ ⊕ _ ; refl },
end

structure except_t (f : Type u → Type v) (α : Type u) :=
 (run : f (string ⊕ α))

open has_map functor
def except_t.map {F} [functor F] {α β} (f : α → β) : except_t F α → except_t F β
 | ⟨ x ⟩ := ⟨ @has_map.map _ sum.functor.to_has_map _ _ f <$> x ⟩

lemma map_comp' {f : Type u → Type v} [functor f] {α β γ : Type u} (g : β → γ) (h : α → β) :
  map g ∘ map h = (map (g ∘ h) : f α → f γ) :=
by funext x ; rw [map_comp]

lemma map_id' {f : Type u → Type v} [functor f] {α} :
  (map id : f α → f α) = id :=
by funext x ; rw [id_map,id]

example {α : Type u} {f : Type u → Type w} [functor f] : functor (except_t f) :=
begin
  refineS { map := @except_t.map _ _ } with law
  ; intros ; casesm except_t f _ ; simp [except_t.map,map_id'],
  rw [← law,map_comp'],
end

example {α : Type u} : functor.{v} (sum α) :=
  -- (we use `.{v}` above so that Lean won't have to guess the universes which would
  -- create visual noise
begin
  (do let e : pexpr := ``({ map := sum.map_right }),
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      trace struct_n,
        -- what are the fields of `functor`?
      env ← get_env,
      trace $ env.structure_fields struct_n),
    -- prints:
    -- functor
    -- (some [to_has_map, map_const_eq, id_map, map_comp])
  -- refine { map := sorry, .. },
  -- refineS { map := sorry },
  -- (do fs ← expanded_field_list `applicative,
  --     trace fs ),
  refineS { map := @sum.map_right _, .. } with field,
  -- field map_const_eq { dunfold has_map.map, tactic.apply_auto_param },
  field map_comp { intros, casesm _ ⊕ _ ; refl },
  field id_map { intros, casesm _ ⊕ _ ; refl },
  -- trace_result
  -- (do let e : pexpr := ``({ map := @sum.map_right _ }),
  --     str ← e.get_structure_instance_info,
  --     tgt ← target,
  --     let struct_n : name := tgt.get_app_fn.const_name,
  --     exp_fields ← expanded_field_list struct_n,
  --     let missing_f := exp_fields.diff str.field_names,
  --     vs ← mk_mvar_list missing_f.length,
  --     trace str.field_values,
  --     trace str.field_names,
  --     trace missing_f,
  --     let e' : pexpr := pexpr.mk_structure_instance
  --         { struct := some struct_n
  --         , field_names := str.field_names ++ missing_f
  --         , field_values := str.field_values ++ vs.map to_pexpr },
  --     trace e',
  --     refine e'),
  -- admit,
end
