let nat_scope = {|
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
  %term addZ {{X}} add X %(z nat) X
  %term addS {{X Y Z}} %if add X (%(S nat) Y) (%(S nat) Z) %<- add X Y Z
%}

%mode add %in %in %out
%worlds () (add _ _ _)
%total X (add X _ _)
|}
