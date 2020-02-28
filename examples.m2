-- automotically construct the Jordan and Monster fusion tables
JordanTable = n -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,n} => set {n},
    {0,1} => set {}, {0,0} => set {0}, {0,n} => set {n},
    {n,1} => set {n}, {n,0} => set {n}, {n,n} => set {1,0}
}
MonsterTable = (a,b) -> hashTable {
    {r#1,r#1} => set {r#1}, {r#1,r#0} => set {}, {r#1,a} => set {a}, {r#1,b} => set {b},
    {r#0,r#1} => set {}, {r#0,r#0} => set {r#0}, {r#0,a} => set {a}, {r#0,b} => set {b},
    {a,r#1} => set {a}, {a,r#0} => set {a}, {a,a} => set {r#1,r#0}, {a,b} => set {b},
    {b,r#1} => set {b}, {b,r#0} => set {b}, {b,a} => set {b}, {b,b} => set {r#1, r#0, a}
}

OtherMonsterTable = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,1/2} => set {1/2}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {a}, {a,1/2} => set {1/2}, {a,b} => set {b},
    {1/2,1} => set {1/2}, {1/2,a} => set {1/2}, {1/2,1/2} => set {1,a}, {1/2,b} => set {b},
    {b,1} => set {b}, {b,a} => set {b}, {b,1/2} => set {b}, {b,b} => set {1, a, 1/2}
}


RestrictedMonsterTable = (a,b) -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,a} => set {a}, {1,b} => set {b},
    {0,1} => set {}, {0,0} => set {0}, {0,a} => set {a}, {0,b} => set {b},
    {a,1} => set {a}, {a,0} => set {a}, {a,a} => set {1,0}, {a,b} => set {},
    {b,1} => set {b}, {b,0} => set {b}, {b,a} => set {}, {b,b} => set {1, 0}
}

InfiniteFamilyTable = a -> hashTable{
    {1,1} => set {1}, {1,0} => set {}, {1,1/2} => set {1/2}, {1,3/8} => set {3/8}, {1, a} => set {a},
    {0,1} => set {}, {0,0} => set {0}, {0,1/2} => set {1/2}, {0,3/8} => set {3/8}, {0, a} => set {a},
    {1/2,1} => set {1/2}, {1/2,0} => set {1/2}, {1/2,1/2} => set {1,0}, {1/2,3/8} => set {3/8}, {1/2, a} => set {a},
    {3/8,1} => set {3/8}, {3/8,0} => set {3/8}, {3/8,1/2} => set {3/8}, {3/8,3/8} => set {1, 0, 1/2}, {3/8,a} => set {},
    {a, 1} => set {a}, {a, 0} => set {a}, {a, 1/2} => set {a}, {a, 3/8} => set {}, {a, a} => set {1, 0, 1/2}
}

GenericJordan = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {a}, {a,b} => set {b},
    {b,1} => set {b}, {b,a} => set {b}, {b,b} => set {1, a}
}

ThreeEvals = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {1,a}, {a,b} => set {b},
    {b,1} => set {b}, {b,a} => set {b}, {b,b} => set {1, a}
}

ThreeEvalsMax = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {1,a,b}, {a,b} => set {1,a,b},
    {b,1} => set {b}, {b,a} => set {1,a,b}, {b,b} => set {1,a,b}
}

ThreeEvalsOther = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {1}, {a,b} => set {1},
    {b,1} => set {b}, {b,a} => set {1}, {b,b} => set {1}
}

C3Graded = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {b}, {a,b} => set {1},
    {b,1} => set {b}, {b,a} => set {1}, {b,b} => set {a}
}

C2Graded = (a,b) -> hashTable {
    {1,1} => set {1}, {1,a} => set {a}, {1,b} => set {b},
    {a,1} => set {a}, {a,a} => set {1}, {a,b} => set {1},
    {b,1} => set {b}, {b,a} => set {1}, {b,b} => set {1}
}

GenericJordanNilpotent = (a,b) -> hashTable {
    {0,0} => set {0}, {0,a} => set {a}, {0,b} => set {b},
    {a,0} => set {a}, {a,a} => set {a}, {a,b} => set {b},
    {b,0} => set {b}, {b,a} => set {b}, {b,b} => set {0, a}
}

GenericMonsterNilpotent = (a,b,c) -> hashTable {
    {0,0} => set {0}, {0,a} => set {}, {0,b} => set {b}, {0,c} => set {c},
    {a,0} => set {}, {a,a} => set {a}, {a,b} => set {b}, {a,c} => set {c},
    {b,0} => set {b}, {b,a} => set {b}, {b,b} => set {0,a}, {b,c} => set {c},
    {c,0} => set {c}, {c,a} => set {c}, {c,b} => set {c}, {c,c} => set {0, a, b}
}

twoEvals = n -> hashTable {
    {1, 1} => set {1}, {1, n} => set {n},
    {n, 1} => set {n}, {n, n} => set {1,n}
}

twoEvalsNilpotent = n -> hashTable {
    {0, 0} => set {0}, {0, n} => set {n},
    {n, 0} => set {n}, {n, n} => set {0,n}
}

ThreeEvalsNilpotent = (a,b) -> hashTable {
    {0,0} => set {0}, {0,a} => set {a}, {0,b} => set {b},
    {a,0} => set {a}, {a,a} => set {0,a}, {a,b} => set {b},
    {b,0} => set {b}, {b,a} => set {b}, {b,b} => set {0, a}
}


tkachev14 = hashTable {
    {1,1} => set {1},
    {1, -1} => set {-1},
    {1, -1/2} => set {-1/2},
    {1, 1/2} => set {1/2},

    {-1, 1} => set {-1},
    {-1, -1} => set {1},
    {-1, -1/2} => set {1/2},
    {-1, 1/2} => set {-1/2, 1/2},

    {-1/2, 1} => set {-1/2},
    {-1/2, -1} => set {1/2},
    {-1/2, -1/2} => set {1, -1/2} ,
    {-1/2, 1/2} => set {-1, 1/2},

    {1/2, 1} => set {1/2},
    {1/2, -1} => set {1/2, -1/2},
    {1/2, -1/2} => set {-1, 1/2},
    {1/2, 1/2} => set {1, -1, -1/2}
}

tkachev14graded = hashTable {
    {1,1} => set {1},
    {1, -1} => set {-1},
    {1, -1/2} => set {-1/2},
    {1, 1/2} => set {1/2},

    {-1, 1} => set {-1},
    {-1, -1} => set {1},
    {-1, -1/2} => set {},
    {-1, 1/2} => set {1/2},

    {-1/2, 1} => set {-1/2},
    {-1/2, -1} => set {},
    {-1/2, -1/2} => set {1, -1/2} ,
    {-1/2, 1/2} => set {1/2},

    {1/2, 1} => set {1/2},
    {1/2, -1} => set {1/2},
    {1/2, -1/2} => set {1/2},
    {1/2, 1/2} => set {1, -1, -1/2}
}

tkachev14gradedsubtable = hashTable {
    {1,1} => set {1},
    {1, -1} => set {-1},
    {1, -1/2} => set {-1/2},

    {-1, 1} => set {-1},
    {-1, -1} => set {1},
    {-1, -1/2} => set {},

    {-1/2, 1} => set {-1/2},
    {-1/2, -1} => set {},
    {-1/2, -1/2} => set {1, -1/2}
}

tkachev16 = n -> hashTable {
    {1, 1} => set {1}, {1, n} => set {n},
    {n, 1} => set {n}, {n, n} => set {1}
}

tkachev17 = n -> hashTable {
    {1, 1} => set {1}, {1, n} => set {n},
    {n, 1} => set {n}, {n, n} => set {1,n}
}

tkachev32 = hashTable {
    {1,1} => set {1}, {1,-1} => set {-1}, {1, 1/2} => set {1/2},
    {-1,1} => set {-1}, {-1,-1} => set {1}, {-1, 1/2} => set {1/2},
    {1/2,1} => set {1/2}, {1/2,-1} => set {1/2}, {1/2, 1/2} => set {1, -1}
}

Harada = hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1, -1} => set {-1}, {1, 4/3} => set {4/3}, {1, -2/3} => set {-2/3},
    {0,1} => set {}, {0,0} => set {0}, {0,-1} => set {}, {0, 4/3} => set {4/3}, {0,-2/3} => set {-2/3},
    {-1,1} => set {-1}, {-1,0} => set {}, {-1,-1} => set {1}, {-1, 4/3} => set {}, {-1, -2/3} => set {-2/3},
    {4/3, 1} => set {4/3}, {4/3, 0} => set {4/3}, {4/3, -1} => set {}, {4/3, 4/3} => set {1,0}, {4/3, -2/3} => set {-2/3},
    {-2/3, 1} => set {-2/3}, {-2/3, 0} => set {-2/3}, {-2/3, -1} => set {-2/3}, {-2/3, 4/3} => set {-2/3}, {-2/3, -2/3} => set {1,0,-1}
}
