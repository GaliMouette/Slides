H  : length nat [] = 0
H1 : forall x xs,
       length nat (x::xs) = length nat xs + 1
-----------------------------
length nat [1; 2; 3] = 3
