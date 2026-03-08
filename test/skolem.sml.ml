open! Basis;;

Twelf.reset ();;
Twelf.loadFile "TEST/cp.elf";;

let (Some cpt) = Names.nameLookup "cpt"
let _ = Skolem.install [ cpt ]
let (Some cpt1) = Names.nameLookup "cpt#1"
let (Some cpt2) = Names.nameLookup "cpt#2"

let _ =
  TextIO.print (Print.expToString (IntSyn.null_, IntSyn.constType cpt1) ^ "\n")

let _ =
  TextIO.print (Print.expToString (IntSyn.null_, IntSyn.constType cpt2) ^ "\n")
