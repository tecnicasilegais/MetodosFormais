//Integrantes:
//Eduardo Andrade, Marcelo Heredia, Michael Rosa
class {:autocontracts} Stack
{
    ghost const maxLen: int;
    ghost var data: seq<int>;

    var arr: array<int>;
    var max: int;
    var head: int; //position

    predicate Valid()
    {
        max > 0 &&
        arr.Length == max &&
        maxLen == max &&
        0 <= head <= max &&
        data == arr[0..head]
    }

    constructor(n: int)
    requires n > 0
    ensures maxLen == n
    ensures data == []
    {
        max := n;
        arr := new int[n];
        head := 0;

        //spec
        maxLen := n;
        data := [];
    }

    method Push(e: int) returns (b: bool)
    ensures old(|data|) < maxLen ==> data == old(data) + [e] && b == true
    ensures old(|data|) >= maxLen ==> data == old(data) && b == false
    {
        if head < max
        {
            arr[head] := e;
            head := head + 1;

            //spec
            data := data + [e];

            return true;
        }
        return false;
    }

    method Pop() returns (e: int)
    requires |data|>0
    ensures data == old(data[0..|data|-1])
    ensures e == old(data)[|data|]
    {
        head := head - 1;
        e := arr[head];

        //spec
        data := arr[0..head];
    }

    method Drop()
    ensures old(|data|)>0 ==> data == old(data[0..|data|-1])
    {
        if head > 0
        {
            head := head -1;

            //spec
            data := arr[0..head];
        }
    }

    method Top() returns (e: int)
    requires |data| > 0
    ensures data == old(data)
    ensures e == data[|data|-1]
    {
        return arr[head-1];
    }

    method Full() returns (b: bool)
    ensures data == old(data)
    ensures b == (|data| == maxLen)
    {
        return head == max;
    }

    method Empty() returns (b: bool)
    ensures data == old(data)
    ensures b == (|data| == 0)
    {
        return head==0;
    }

    method Count() returns (n: int)
    ensures data == old(data)
    ensures n == |data|
    {
        n := head;
    }

    method Capacity() returns (s: int)
    ensures data == old(data)
    ensures s == maxLen
    {
        s := max;
    }

    method Reverse()
    ensures |data| == old(|data|)
    ensures reversed(data, old(data))
    {
        var novo := new int[arr.Length];
	    var tam := head-1;
	    forall i | 0 <= i <= tam
	    {
		    novo[i] := arr[tam-i];
	    }

	    arr := novo;
        data := arr[0..head];
    }
}

predicate reversed(sq1: seq<int>, sq2: seq<int>)
requires |sq1| == |sq2|
{
    forall i :: 0 <= i < |sq1| ==> sq1[i] == sq2[|sq2|-1-i]
}
method Main()
{
    var s := []; 
    var t := [];
    assert reversed(s,t); //validate predicate for empty 
    s := [1,2];
    t := [2,1];
    assert reversed(s,t); //validate predicate for not empty

    var stack := new Stack(4);
    var cap := stack.Capacity();
    assert cap == 4; 

    var empt := stack.Empty();
    assert empt; 

    var full := stack.Full();
    assert !full;

    var push := stack.Push(1);
    assert push == true;
    push := stack.Push(2);
    assert push == true;
    push := stack.Push(3);
    assert push == true;
    push := stack.Push(4);
    assert push == true; //max = 4

    push := stack.Push(5);
    assert push == false; //should not push anymore

    empt := stack.Empty();
    assert !empt;

    full := stack.Full();
    assert full;

    var count := stack.Count();
    assert count == 4;

    var top := stack.Top();
    assert top == 4;
    assert stack.data == [1,2,3,4];
    
    stack.Reverse();
    assert stack.data == [4,3,2,1];

    stack.Drop();
    assert stack.data == [4,3,2];

    var pop := stack.Pop();
    assert pop == 2;
    assert stack.data == [4,3];
    
}