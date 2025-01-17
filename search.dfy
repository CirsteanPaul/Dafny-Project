include "utils.dfy"

method BadCharHeuristic(pattern: seq<char>, badChar: array<int>)
    requires badChar.Length == 256
    requires forall i :: 0 <= i < |pattern| ==> pattern[i] as int <= 255
    modifies badChar
    ensures forall i :: 0 <= i < |pattern| ==> badChar[pattern[i] as int] != -1
    ensures forall i :: 0 <= i < badChar.Length ==> badChar[i] < |pattern|
{
    var NO_OF_CHARS := 256;

    // Initialize all occurrences as -1
    for i := 0 to badChar.Length 
        invariant forall ii :: 0 <= ii < i ==> badChar[ii] == -1
    {
        badChar[i] := -1;
    }

    // Fill the actual value of the last occurrence
    for i := 0 to |pattern|
        invariant forall ii :: 0 <= ii < i ==> badChar[pattern[ii] as int] != -1
        invariant forall ii :: 0 <= ii < badChar.Length ==> badChar[ii] < |pattern|
    {
        badChar[pattern[i] as int] := i;
    }
}

method Search(text: seq<char>, pattern: seq<char>) returns (foundIndices: seq<nat>)
    requires forall i :: 0 <= i < |pattern| ==> pattern[i] as int <= 255
    requires forall i :: 0 <= i < |text| ==> text[i] as int <= 255
    requires |pattern| <= |text|
    requires |pattern| >= 1
    ensures forall ii :: 0 <= ii < |foundIndices| ==> foundIndices[ii] <= |text| - |pattern| && foundIndices[ii] >= 0
    ensures forall ii :: 0 <= ii < |foundIndices| ==> text[foundIndices[ii] .. foundIndices[ii] + |pattern|] == pattern
    ensures forall ii :: 0 <= ii < |text| - |pattern| ==> text[ii .. ii + |pattern|] != pattern ==> ii !in foundIndices

{
    var NO_OF_CHARS := 256;
    foundIndices := [];
    var totalShifts := 0;

    var badChar := new int[NO_OF_CHARS];

    // Fill the bad character array
    BadCharHeuristic(pattern, badChar);

    print "Text: ";
    print text;
    print "\n";

    print "Pattern: ";
    print pattern;
    print "\n";

    print "Index | Substring  | Match      | Shift\n";
    print "----------------------------------------\n";

    var s := 0; // s is the shift of the pattern relative to text

    while s <= |text| - |pattern| 
        decreases |text| - |pattern| - s
        invariant forall i :: 0 <= i < badChar.Length ==> badChar[i] < |pattern|
        invariant forall ii :: 0 <= ii < |foundIndices| ==> foundIndices[ii] <= |text| - |pattern| && foundIndices[ii] >= 0
        invariant forall ii :: 0 <= ii < |foundIndices| ==> text[foundIndices[ii] .. foundIndices[ii] + |pattern|] == pattern
        invariant forall ii :: 0 <= ii < s && s <= |text| - |pattern| ==> text[ii .. ii + |pattern|] != pattern ==> ii !in foundIndices // Should be if it is pattern => in foundIndices
    {

        var j := |pattern| - 1;
 
        var substring := text[s .. s + |pattern|];

        print s, "      | \"", substring, "\"";
        // Reduce index j while characters match
        while j >= 0 && pattern[j] == text[s + j] 
            decreases j
            invariant j + 1 >= 0 && |pattern| - 1 >= 0
            invariant j != |pattern| - 1 ==> pattern[j + 1 .. |pattern|] == text[s + j + 1 .. s + |pattern|]
            invariant j == -1 ==> text[s .. s + |pattern|] == pattern
        {
            j := j - 1;
        }
        
        if j < 0 {
            print " | Found      | 0\n";
            
            foundIndices := foundIndices + [s];            

            // Shift the pattern
            if s + |pattern| < |text| {
                s := s + |pattern| - badChar[text[s + |pattern|] as int];
            } else {
                s := s + 1;
            }
        }
        else {
            var aux := max(1, j - badChar[text[s + j] as int]); 
            print " | Not Found  | ", aux, "\n";
            s := s + aux;
        }

        totalShifts := totalShifts + 1;
    }

    
    print "----------------------------------------\n";
    print "Summary:\n";
    print "- Pattern found at indices: ", foundIndices, "\n";
    print "- Total shifts: ", totalShifts, "\n";
    print "Pattern matching completed.\n";
}