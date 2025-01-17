method max(a: int, b: int) returns (maxVal: int)
    ensures maxVal >= a && maxVal >= b
{
    if a > b {
        maxVal := a;
    } else {
        maxVal := b;
    }
}