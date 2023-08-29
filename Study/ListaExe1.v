(*
Nenhum outro arquivo deve ser importado.

Nome: Vinícios Bidin Santos
*)

Require Import Coq.Arith.PeanoNat.

(* Podemos definir uma representação binária dos números naturais por meio de dois
construtores que representam 0s e 1s (B0 e B1), e um marcador de final da sequência Z.

Por exemplo:


				decimal               Binary                          unary
					 0                    B0 Z                              O
					 1                    B1 Z                            S O
					 2                B0 (B1 Z)                        S (S O)
					 3                B1 (B1 Z)                     S (S (S O))
					 4            B0 (B0 (B1 Z))                 S (S (S (S O)))
					 5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
					 6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
					 7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
					 8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

Note que o bit menos significativo fica a esquerda da sequência.

*)

Theorem add_0_r : forall n: nat, n + 0 = n.
Proof.
intros n. induction n.
	- (* n = 0 *)    reflexivity.
	- (* n = S n' *) simpl. rewrite -> IHn. reflexivity.
Qed.

Inductive bin: Type :=
	| Z
	| B0 (n : bin)
	| B1 (n : bin)
.

Theorem add_comm : forall n m : nat,
	n + m = m + n.
Proof.
	induction n.
	- intros m. simpl. rewrite add_0_r. reflexivity.
	- intros m. simpl. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.

(* Complete as definições abaixo, sendo incr uma função que incrementa um número
binário e bin_to_nat a função que converte um binário em natural: *)

Fixpoint incr (m: bin): bin :=
	match m with
	| Z => B1 Z
	| B0 b => B1 b
	| B1 b => B0 (incr b)
	end
.

Fixpoint bin_to_nat (m: bin): nat :=
	match m with
	| Z => O
	| B0 b => 2 * (bin_to_nat b)
	| B1 b => S (2 * (bin_to_nat b))
	end
.

(* Declare uma função que converta natural para binário: *)

Fixpoint nat_to_bin (n: nat): bin :=
	match n with
	| O => Z
	| S n' => incr (nat_to_bin n')
	end
.

(* Prove que as tranformações definididas no diagrama abaixo são válidas:

													 incr
							bin ----------------------> bin
							 |                           |
		bin_to_nat |                           |  bin_to_nat
							 |                           |
							 v                           v
							nat ----------------------> nat
														 S

*)

Theorem bin_to_nat_pres_incr: forall b: bin,
	bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
	intros. induction b.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl. rewrite add_0_r.
		rewrite add_0_r. rewrite IHb.
		simpl. rewrite add_comm.
		assert (S (bin_to_nat b) + bin_to_nat b = S (bin_to_nat b + bin_to_nat b)).
			{
				simpl. reflexivity.
			}
		rewrite H. reflexivity.
Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite bin_to_nat_pres_incr. simpl. rewrite IHn. reflexivity.
Qed.
