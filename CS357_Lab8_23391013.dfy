// Q1l: Max and Min methods

function MaxDef(a: int, b: int): int
{
    if a > b then a else b
}

function MinDef(a: int, b: int): int
{
    if a < b then a else b
}

method Max(a : int, b : int) returns (result:int) 
   ensures result == MaxDef(a,b) 
{
    if a > b {
        result := a;
    } 
    else {
        result := b;
    }
} 

method Min(a : int, b : int) returns (result : int) 
    ensures result == MinDef(a,b) 
{
    if a < b {
        result := a; 
    } 
    else {
        result := b;
    }
}

// Q2: Recursive Power Functions 

function pow2(n : nat) : nat 
{
    if n == 0 then 
    1
    else 
    2*pow2(n-1) 
} 

function pow(a : int, n : nat) : int 
{
    if n == 0 then 
    1 
    else 
    a * pow (a, n-1)
} 

// Q3: Power Method with Specification 

method Pow (a : int, n : nat) returns (result : int) 
   ensures result == pow(a,n) 
{
    result := 1; 
    var i := 0; 
    while i < n 
         invariant 0 <= i <= n
         invariant result == pow(a,i)
    {
        result := result * a;  
        i := i + 1; 
    }
} 

// Q4: GCD Decreases Clause 
function gcd(a : int, b : int): int 
    requires a > 0 && b > 0 
    decreases a+b 
{
    if a==b then 
       a
    else if b > a then 
       gcd(b - a, a) 
    else 
       gcd(b, a - b)
}

//Q5: Binary Search Specification 

predicate sorted(a : array<int>) 
        reads a 
{
    forall i, j | 0 <= i < j < a.Length :: a[i] <= a[j]
} 

method BinarySearch(a : array<int>, value : int) returns (index : int) 
       requires sorted(a) 
       ensures index == -1 || 0 <= index < a.Length
       ensures index == -1 ==> value !in a[..] 
       ensures index >=0 ==> a[index] == value 
{
    var low := 0; 
    var high := a.Length; 

    while low < high 
          invariant 0 <=low<=high<=a.Length
          invariant value !in a[..low] && value !in a[high..]
    {
        var mid := (high+low)/2; 

        if a[mid] < value {
            low := mid+1; 
        } 
        else if a[mid] > value {
            high := mid;
        } 
        else {
            return mid;
        }
    } 
    index := -1;
}