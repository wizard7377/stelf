#import "@preview/frame-it:2.0.0": *
#let kind_pi(name: [], arg, res) = $Pi_#name #arg dot #res$
#let type_pi(name: [], arg, res) = $forall_#name #arg dot #res$

#let sort = frame("Sort", green)
#show: frame-style(styles.boxy)

