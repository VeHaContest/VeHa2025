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
  (integerp n) (integerp a) (integerp b) (integerp k) 
  (integerp m) (integerp i) (integerp j) (integerp c) 
  (integerp f) (integerp e) (integerp p) (integerp g)
  (integerp h) (integerp u) (integerp v) (integerp d)
  (integerp l) (integerp o) (integerp q) (integerp r)
  (integerp s) (integerp t) (integerp w) (integerp x)
  (integerp y) (integerp z)
  (< 0 n)
  (equal (- (* a a) (* n b b)) k)
  (implies (not (equal f 0)) 
           (and 
             (not (equal c 0))
             (not (equal k 0))
             (equal (+ (* h m) (* v n)) (* a c))
             (equal (+ h (* m v)) (* b c))
             (equal (- (* m m) n) (* k c))
             (equal (- (* h j) (* v n)) (* g c))
             (equal (- (* v j) h) (* u c))
             (integerp (/ (+ m j) c))
             (equal (- (* h h) (* n v v)) (* g k))
             (equal (- (* a a) (* n b b)) k)))
  (implies (equal e 1) 
           (and 
             (integerp (/ (+ m p) k))
             (not (equal (* p p) n))))
  (implies (equal f 0) 
           (and (equal a 1) (equal b 0) (equal k 1) 
                (equal c 1) (equal m 0) (equal j 0)))
  (implies (and (equal k 1) (equal f 1))
           (equal (- (* a a) (* n b b)) 1))
  (or (equal f 0) (equal f 1))
  (implies (and (not (equal f 0)) (not (equal k 0)))
           (and (equal (- (* h h) (* n v v)) (* g k))
                (equal (- (* a a) (* n b b)) k)))
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
