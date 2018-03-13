

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

open interactive interactive.types
#print structure_instance_info
meta def tactic.interactive.refineS (e : parse texpr) : tactic unit :=
do    str ← e.get_structure_instance_info,
      trace str.struct,
      trace str.sources,
      trace str.field_names,
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      env ← get_env,
      exp_fields ← env.structure_fields struct_n,
      let missing_f := (exp_fields.diff str.field_names).diff [`to_has_map],
      vs ← mk_mvar_list missing_f.length,
      let e' : pexpr := pexpr.mk_structure_instance
          { -- struct := some struct_n
          -- ,
          field_names := str.field_names ++ missing_f
          , field_values := str.field_values ++ vs.map to_pexpr },
      refine ``(%%e' : %%tgt)

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
  refineS { map := sorry },
  (do let e : pexpr := ``({ map := sum.map_right }),
      str ← e.get_structure_instance_info,
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      env ← get_env,
      exp_fields ← env.structure_fields struct_n,
      let missing_f := exp_fields.diff str.field_names,
      vs ← mk_mvar_list missing_f.length,
      let e' : pexpr := pexpr.mk_structure_instance
          { -- struct := some struct_n
          -- ,
          field_names := str.field_names ++ missing_f
          , field_values := str.field_values ++ vs.map to_pexpr },
      refine e'),
  admit
end
