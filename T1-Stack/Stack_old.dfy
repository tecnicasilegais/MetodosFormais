class Stack{
    var capacity : int; 
    var list : array<int>; 
    var top : int;

    predicate Valid()
    reads this;
    {
        capacity > 0 &&
        capacity < list.Length &&
        -1 <= top < capacity
    }

    predicate Empty()
    reads this;
    {
        top == -1
    }

    predicate Full()
    reads this;
    {
       top == capacity 
    }

    constructor (c : int)
    requires c > 0;
    ensures Empty();
    ensures fresh(list);
    ensures this.list.Length == c;
    ensures capacity == c && top == -1;
    {
        capacity := c;
        list := new int[c];
        top := -1;
    }

    method isEmpty() returns (r:bool)
    requires Empty();
    requires Valid();
    ensures Empty();
    {
        return true;
    }

    method isFull() returns (r:bool)
    requires Full();
    requires Valid();
    ensures Full();
    {
        return true;
    }

    method Peek() returns (r:int)
    requires Valid();
    requires !Empty();
    ensures list == old(list) && r == list[top]
    {
        return list[top];
    }

    
    //method Push (r:int)
    //modifies list, `top;
    //requires Valid();
    //requires !Full();
    //ensures r == list[top];
    //{
    //    top := top+1;
    //    list[top] := r;
    //}
}