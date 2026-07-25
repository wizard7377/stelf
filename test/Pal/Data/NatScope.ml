let nat_scope =
  {|
# Natural Numbers Test

This is going to be (hopefully) a simple test of the natural numbers and scopes

%sort nat %.

## We can use headings whenever we wish

%scope nat %{
  %term z nat
  %term S %pi nat %-> nat
%}

%sort add {_ nat} {_ nat} {_ nat}
%scope add %{
  %term addZ {{X}} add X %(nat z) X
  %term addS {{X Y Z}} %if add X (%(nat S) Y) (%(nat S) Z) %<- add X Y Z
%}

%mode add %in %in %out
%worlds () (add _ _ _)
%total X (add X _ _)
|}
