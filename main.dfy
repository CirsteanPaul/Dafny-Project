method Main() {
    var txt := "ABAAABCD";
    var pat := "ABC";

    search(txt, pat);
}

method search(txt: seq<char>, pat: seq<char>)
    requires |pat| > 2
    requires forall i :: 0 <= i < |pat| ==> pat[i] as int <= 255
{
    var badchar := new int[256];
    badCharHeuristic(pat, badchar);
}

method badCharHeuristic(pat: seq<char>,  badchar: array<int>)
    requires |pat| > 2
    requires badchar.Length == 256
    requires forall i :: 0 <= i < |pat| ==> pat[i] as int <= 255
    modifies badchar
    ensures forall i :: 0 <= i < |pat| ==> badchar[pat[i] as int] != -1
    ensures forall i :: 0 <= i < |pat|  ==> badchar[pat[i] as int] != -1
{

    for i := 0 to badchar.Length 
    {
        badchar[i] := -1;
    }
    
    for i := 0 to |pat| 
        invariant forall ii :: 0 <= ii < i ==> badchar[pat[ii] as int] != -1
    {
        badchar[pat[i] as int] := i;
    }
}

function max(a: int, b: int): int {
    if a > b then a else b
}
