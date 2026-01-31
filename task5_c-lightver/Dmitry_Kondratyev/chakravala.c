/*
(and
    (integerp n)
    (< 0 n)
)
*/
void chakravala(int n, int variables[])
{
    int a = 1;
    int b = 0;
    int m = 0;
    int k = 1;
    int i = 0;
    int j = 0;
    int c = 1;
    int d = 0;
    int e = 0;
    int f = 0;
    int g = 0;
    int h = 0;
    int l = 0;
    int o = 0;
    int p = 0;
    int q = 0;
    int r = 0;
    int s = 0;
    int t = 0;
    int u = 0;
    int v = 0;
    int w = 0;
    int x = 0;
    int y = 0;
    int z = 0;

    /*
    (and
        (integerp n)
        (integerp a)
        (integerp b)
        (integerp k)
        (integerp m)
        (integerp p)
        (integerp i)
        (integerp c)
        (integerp h)
        (integerp v)
        (integerp g)
        (integerp u)
        (integerp j)
        (integerp f)
        (integerp e)
        (< 0 n)
        (not
            (=
                (-
                    (*
                        p
                        p
                    )
                    n
                )
                0
            )
        )
        (implies
            (=
                e
                1
            )
            (integerp
                (/
                    (+
                        m
                        p
                    )
                    k
                )
            )
        )
        (integerp
            (/
                (-
                    (*
                        m
                        m
                    )
                    n
                )
                k
            )
        )
        (or
            (=
                f
                0
            )
            (=
                f
                1
            )
        )
        (implies
            (and
                (=
                    f
                    1
                )
                (not
                    (=
                        c
                        0
                    )
                )
            )
            (and
                (=
                    g
                    (/
                        (-
                            (*
                                h
                                j
                            )
                            (*
                                v
                                n
                            )
                        )
                        c
                    )
                )
                (=
                    u
                    (/
                        (-
                            (*
                                v
                                j
                            )
                            h
                        )
                        c
                    )
                )
                (=
                    h
                    (/
                        (-
                            (*
                                a
                                m
                            )
                            (*
                                b
                                n
                            )
                        )
                        k
                    )
                )
                (=
                    v
                    (/
                        (-
                            (*
                                b
                                m
                            )
                            a
                        )
                        k
                    )
                )
                (=
                    a
                    (/
                        (+
                            (*
                                h
                                m
                            )
                            (*
                                v
                                n
                            )
                        )
                        c
                    )
                )
                (=
                    b
                    (/
                        (+
                            h
                            (*
                                m
                                v
                            )
                        )
                        c
                    )
                )
                (=
                    k
                    (/
                        (-
                            (*
                                m
                                m
                            )
                            n
                        )
                        c
                    )
                )
            )
        )
        (=
            (-
                (*
                    a
                    a
                )
                (*
                    n
                    (*
                        b
                        b
                    )
                )
            )
            k
        )
    )
    */
    while (k != 1 || f != 1)
    {
        if (k != 0 && c != 0)
        {
            r = m + i;
            x = r / k;
            y = k * x;
            q = r - y;

            if (q == 0)
            {
                o = i*i;
                o = o-n;
                if (o != 0)
                {
                    if (o > 0)
                    {
                        s = m;
                        if (e == 1)
                        {
                            l = p*p;
                            l =  n - l;
                            if (o < l)
                            {
                                m = i;
                            }
                            else
                            {
                                m = p;
                            }
                        }
                        else
                        {
                            m = i;
                        }
                    
                        if (f == 0)
                        {
                            j = m;
                            a = m;
                            b = 1;
                            h = 1;
                            v = 0;
                            g = m;
                            u = -1;
                            f = 1;
                            c = 1;
                            k = m * m;
                            k = k - n;
                        }
                        else
                        {
                            if (f == 1)
                            {
                                j = s;
                                g = h;
                                h = a;
                                u = v;
                                v = b;
                                w = m + j;
                                c = k;
                                z = w / c;
                                a = h*z;
                                b = v*z;
                                a = a - g;
                                b = b - u;
                                k = z*w;
                                d = 2*j;
                                d = d*z;
                                k = k - d;
                                t = j*j;
                                t = t - n;
                                t = t / c;
                                k = k + t;
                            }
                            else
                            {
                                a = 1;
                                b = 0;
                                c = 1;
                                f = 1;
                            }    
                        }
                        e = 0;
                        i = 0;
                    }
                    else
                    {
                        e = 1;
                        p = i;
                        i = i + 1;
                    }
                }
                else
                {
                    a = 1;
                    b = 0;
                    c = 0;
                    k = 1;
                }
            }
            else
            {
                i = i + 1;
            }
        }
        else
        {
            a = 1;
            b = 0;
            c = 0;
            k = 1;
            f = 1;
        }
    }

    variables[0] = a;
    variables[1] = b;
}
/*
(=
    (-
        (*
            a
            a
        )
        (*
            n
            (*
                b
                b
            )
        )
     )
     1
)
*/
