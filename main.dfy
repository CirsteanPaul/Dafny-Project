include "search.dfy"

method Main()
{
    var text := "AABAACAADAABAAABAA";
    var pattern := "AAB";

    print "Starting Boyer-Moore Pattern Matching\n";
    print "------------------------------------\n";

    var _ := Search(text, pattern);
}
