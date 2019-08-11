-- automotically construct the Jordan and Monster fusion tables
JordanTable = n -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,n} => set {n},
    {0,1} => set {}, {0,0} => set {0}, {0,n} => set {n},
    {n,1} => set {n}, {n,0} => set {n}, {n,n} => set {1,0}
}
MonsterTable = (a,b) -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,a} => set {a}, {1,b} => set {b},
    {0,1} => set {}, {0,0} => set {0}, {0,a} => set {a}, {0,b} => set {b},
    {a,1} => set {a}, {a,0} => set {a}, {a,a} => set {1,0}, {a,b} => set {b},
    {b,1} => set {b}, {b,0} => set {b}, {b,a} => set {b}, {b,b} => set {1, 0, a}
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
