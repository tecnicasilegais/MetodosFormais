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

    predicate isEmpty()
    reads this;
    {
        top == -1
    }

    predicate isFull()
    reads this;
    {
       top == capacity 
    }

    constructor (c : int)
    requires c > 0;
    ensures isEmpty();
    ensures fresh(list);
    ensures this.list.Length == c;
    ensures capacity == c && top == -1;
    {
        capacity := c;
        list := new int[c];
        top := -1;
    }
}