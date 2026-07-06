import DedekindReals.Harness

open DedekindReals

#guard Qmin4 1 2 3 4 == (1 : Rat)
#guard Qmax4 1 2 3 4 == (4 : Rat)
#guard sum_f_Q0 (fun n => (n : Rat)) 2 == (3 : Rat)
