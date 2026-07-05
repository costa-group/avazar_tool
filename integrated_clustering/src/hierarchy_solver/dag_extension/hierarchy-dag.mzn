include "globals.mzn";

int: n;
set of int: N = 1..n;

int: num_fixed_arcs;
set of int: FIXED_ARCS = 1..num_fixed_arcs;

array[FIXED_ARCS, 1..2] of N: fixed_arcs;

int: num_var_arcs;
set of int: VAR_ARCS = 1..num_var_arcs;

array[VAR_ARCS, 1..2] of N: var_arcs;
array[VAR_ARCS] of var bool: enabled;

constraint dag(
  fixed_arcs[.., 1] ++ var_arcs[.., 1],
  fixed_arcs[.., 2] ++ var_arcs[.., 2],
  [true | _ in N],
  [true | _ in FIXED_ARCS] ++ [enabled[i] | i in VAR_ARCS]
);

solve maximize sum(enabled);

output [
  %% "(" ++ show(e-1) ++ ", " ++ show(var_arcs[e, ..]) ++ ", " ++ show(enabled[e]) ++ ")\n"
  show(if enabled[e] then 1 else 0 endif)
  | e in VAR_ARCS
];