colorlist = RandomSample[{
    Red, Orange, Yellow, Green,
    Blue, Purple, Brown, Pink,
    Cyan, Magenta, Gray, LightGreen,
    LightBlue, LightGray, LightCyan, LightMagenta,
    LightYellow, LightOrange, Darker[Red], Darker[Blue], 
    Darker[Yellow], Darker[Green], Darker[Purple], Darker[Pink], 
    Darker[Brown], Darker[White], Darker[Orange], Darker[Magenta], 
    Darker[Cyan], Lighter[Red], Lighter[Orange], Lighter[Purple]}];

GetRandomBrick[] := {colorlist[[1]], RandomInteger[{10, 12}], 
  colorlist[[2]]}

separate[brick_, 
  i_] := {{brick[[1]], brick[[2]], 
   colorlist[[i + 2]]}, {colorlist[[i + 2]], brick[[2]], brick[[3]]}}


split[brick_, 
  diff_] := {{brick[[1]], brick[[2]] - diff, brick[[3]]}, {brick[[1]],
    diff, brick[[3]]}}



randomfunc[brick_, {nb_, color_}] := 
 If[brick[[2]] > 2, 
  RandomInteger[{0, 1}] /. {0 -> separate[brick, color], 
    1 -> split[brick, nb]}, separate[brick, color]]

items[n_, brick_] := 
 FoldList[
   randomfunc[
     Last[#1], {#1[[2]][[2]] - RandomInteger[{1, 2}], #2}] &, {{}, 
    brick}, Range[3, n + 2]][[2 ;; n]]

shuffleitems[list_] := 
 RandomSample[Catenate[{First /@ list, {Last[Last[list]]}}]]


void = {Black, 0, Black};
isvoid[block_] := (block[[1, 2]] == 0) || (TrueQ[
    block[[1, 1]] == block[[1, 3]]])

simplify[block_ /; isvoid[block]] := {void, block[[2]]}
simplify[
  block_ /; block[[1, 2]] < 0] := {{block[[1, 3]], -block[[1, 2]], 
   block[[1, 1]]}, block[[2]]}
simplify[block_] := block


shuffle[w_, h_, l_] := 
 simplify /@ 
  Transpose[{shuffleitems[items[w*h, l]], 
    Flatten[Table[{i, j}, {i, w - 1, 0, -1}, {j, 0, h - 1}], 1]}]


width = 5;
height = 5;
blockheight = 4;

CreateBlocks[] := 
 Catenate[{Flatten[
    Table[{void, {i, j}}, {i, height - 1, blockheight, -1}, {j, 0, 
      width - 1}], 1], shuffle[blockheight, width, GetRandomBrick[]]}]

Blocks = CreateBlocks[];
InitialBlocks = Blocks;

CombineLeft[vector1_, vector2_] := {vector1, vector2} /. {
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x1_, n2_, x2_}, {c_, 
       d_}}} -> {{{x1, n1 + n2, x2}, {a, b}}, {void, {c, d}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x2_, n2_, x1_}, {c_, 
       d_}}} -> {{{x1, n1 - n2, x2}, {a, b}}, {void, {c, d}}},
   {{{x1_, n_, x2_}, {a_, b_}}, {{x2_, n_, x3_}, {c_, d_}}} -> {{{x1, 
       n, x3}, {a, b}}, {void, {c, d}}},
   {{{x2_, n2_, x3_}, {c_, d_}}, {{x1_, n1_, x2_}, {a_, 
       b_}}} -> {{{x1, Min[n1, n2], x3}, {a, 
       b}}, {{If[n1 > n2, x1, x2], Abs[n2 - n1], 
       If[n1 > n2, x2, x3]}, {c, d}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x2_, n2_, x3_}, {c_, 
       d_}}} -> {{{x1, Min[n1, n2], x3}, {a, 
       b}}, {{If[n1 > n2, x1, x2], Abs[n2 - n1], 
       If[n1 > n2, x2, x3]}, {c, d}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x3_, n2_, x4_}, {c_, 
       d_}}} -> {{{x3, n2, x4}, {a, b}}, {{x1, n1, x2}, {c, d}}}}

CombineRight[vector1_, vector2_] := {vector1, vector2} /. {
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x1_, n2_, x2_}, {c_, 
       d_}}} -> {{void, {a, b}}, {{x1, n1 + n2, x2}, {c, d}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x2_, n2_, x1_}, {c_, 
       d_}}} -> {{void, {a, b}}, {{x1, n1 - n2, x2}, {c, d}}},
   {{{x1_, n_, x2_}, {a_, b_}}, {{x2_, n_, x3_}, {c_, 
       d_}}} -> {{void, {a, b}}, {{x1, n, x3}, {c, d}}},
   {{{x2_, n2_, x3_}, {c_, d_}}, {{x1_, n1_, x2_}, {a_, 
       b_}}} -> {{{If[n1 > n2, x1, x2], Abs[n2 - n1], 
       If[n1 > n2, x2, x3]}, {c, d}}, {{x1, Min[n1, n2], x3}, {a, b}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x2_, n2_, x3_}, {c_, 
       d_}}} -> {{{If[n1 > n2, x1, x2], Abs[n2 - n1], 
       If[n1 > n2, x2, x3]}, {c, d}}, {{x1, Min[n1, n2], x3}, {a, b}}},
   {{{x1_, n1_, x2_}, {a_, b_}}, {{x3_, n2_, x4_}, {c_, 
       d_}}} -> {{{x3, n2, x4}, {a, b}}, {{x1, n1, x2}, {c, d}}}}

(*Bloc movement*)

BlockRight[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && Mod[block, fieldwidth] != 0 && 
    isvoid[Blocks[[block + 1]]]] := {Blocks[[block + 1, 1]] = 
   Blocks[[block, 1]], Blocks[[block, 1]] = void, num = num + 1}
BlockRight[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Mod[block, fieldwidth] != 0] :=
 {x = 
   CombineRight[Blocks[[block]], Blocks[[block + 1]]], 
  Blocks[[block]] = x[[1]], Blocks[[block + 1]] = x[[2]], 
  num = num + 1}


BlockLeft[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Mod[block - 1, fieldwidth] != 0 && 
    isvoid[Blocks[[block - 1]]]] := {Blocks[[block - 1, 1]] = 
   Blocks[[block, 1]], Blocks[[block, 1]] = void, num = num - 1}
BlockLeft[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Mod[block - 1, fieldwidth] != 0] := {s = 
   CombineLeft[Blocks[[block - 1]], Blocks[[block]]], 
  Blocks[[block - 1]] = s[[1]], Blocks[[block]] = s[[2]], 
  num = num - 1}

update[] := simplify /@ Blocks

BlockDrop[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && Blocks[[block, 2, 1]] != 0 && 
    isvoid[Blocks[[block + fieldwidth]]]] := {Blocks[[
    block + fieldwidth, 1]] = Blocks[[block, 1]] , 
  Blocks[[block, 1]] = void, num = num + fieldwidth}
BlockDrop[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Blocks[[block, 2, 1]] != 0] := {v = 
   CombineRight[Blocks[[block]], Blocks[[block + fieldwidth]]], 
  Blocks[[block]] = v[[1]], Blocks[[block + fieldwidth]] = v[[2]], 
  num = num + fieldwidth}

BlockLift[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Blocks[[block, 2, 1]] < (height - 1) && 
    isvoid[Blocks[[block - fieldwidth]]]] := {Blocks[[
    block - fieldwidth, 1]] = Blocks[[block, 1]] , 
  Blocks[[block, 1]] = void, num = num - fieldwidth}
BlockLift[{block_, fieldwidth_} /; 
   isvoid[Blocks[[block]]] == False && 
    Blocks[[block, 2, 1]] < (height - 1)] := {t = 
   CombineLeft[Blocks[[block - fieldwidth]], Blocks[[block]]], 
  Blocks[[block - fieldwidth]] = t[[1]], Blocks[[block]] = t[[2]], 
  num = num - fieldwidth}

isNotFinished[] := Count[isvoid /@ Blocks, False] != 1

(*Graphics*)

showgrid[] := 
 Partition[
   Framed /@ 
    Flatten[(First /@ update[]) /. {a_, b_, c_} -> 
       Graphics[{a, Rectangle[{0, 0}, {1, 1}], Black, 
         If[b != 0, Text[Style[b, 30], {1.5, 0.5}], 
          Rectangle[{1, 0}, {2, 1}]], c, Rectangle[{2, 0}, {3, 1}]}], 
     2], width] // Grid

Print[]
Print[]
Print[]
num = width*(height - blockheight) + IntegerPart[width/2] + 
   Mod[width, 2];
initialnum = num;

Grid[{{SetterBar[Dynamic[num], Range[width*height], 
    Enabled -> Dynamic[isNotFinished[]], 
    Appearance -> "Horizontal" -> {Automatic, width}],
   Partition[{"",
      Button["\[UpArrow]", BlockLift[{num, width}], 
       Enabled -> 
        Dynamic[isNotFinished[]] && Dynamic[num > width] && 
         Dynamic[isvoid[Blocks[[num]]] == False]],
      "",
      Button["\[LeftArrow]", BlockLeft[{num, width}], 
       Enabled -> 
        Dynamic[isNotFinished[]] && 
         Dynamic[Mod[num - 1, width] != 0] && 
         Dynamic[isvoid[Blocks[[num]]] == False]],
      "",
      Button["\[RightArrow]", BlockRight[{num, width}], 
       Enabled -> 
        Dynamic[isNotFinished[]] && Dynamic[Mod[num, width] != 0] && 
         Dynamic[isvoid[Blocks[[num]]] == False]],
      "",
      Button["\[DownArrow]", BlockDrop[{num, width}], 
       Enabled -> 
        Dynamic[isNotFinished[]] && 
         Dynamic[num <= width*(height - 1)] && 
         Dynamic[isvoid[Blocks[[num]]] == False]],
      ""}, 3] // Grid,
   Partition[{"",
      Button["Replay", {Blocks = InitialBlocks, num = initialnum}],
      "",
      Button[
       "New Game", {colorlist = RandomSample[colorlist], 
        Blocks = CreateBlocks[], InitialBlocks = Blocks, 
        num = initialnum}]}, 2] // Grid}}, Alignment -> Center]
Print[Dynamic[If[isNotFinished[], "Playing\[Ellipsis]", "You won!"]]]
Print[Dynamic[showgrid[]]]
