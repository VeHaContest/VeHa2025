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
    int t = 0; // случайно случилось так, что t это true в ACL
    int u = 0;
    int v = 0;
    int w = 0;
    int x = 0;
    int y = 0;
    int z = 0;

       //инициализация завершилась   мы не на начальном шаге и не на последнем шаге
  //printf("   a*n  b*n  m_n  k*n  m_n' m_c  k_c      ?i_p ?m_1  a*p  a*c            i_p                      b*p  b_c\n");
  //printf("    a    b    m    k    i    j    c    d    e    f    g    h    l    o    p    q    r    s    t    u    v    w    x    y    z\n");
  //printf("%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d\n",
  //              a,   b,   m,   k,   i,   j,   c,   d,   e,   f,   g,   h,   l,   o,   p,   q,   r,   s,   t,   u,   v,   w,   x,   y,   z);
  /*
    (and
    (integerp a)
    (integerp b)
    (integerp n)
    (integerp m)
    (integerp k)
    (integerp i)
    (integerp j)
    (integerp c)
    (integerp d)
    (integerp e)
    (integerp f)
    (integerp g)
    (integerp h)
    (integerp l)
    (integerp o)
    (integerp p)
    (integerp q)
    (integerp r)
    (integerp t)
    (integerp s)
    (integerp u)
    (integerp v)
    (integerp z)    
    (integerp w)
    (integerp x)
    (integerp y)
    (< 0 n)
    (not (equal (* p p) n))
    (implies (equal e 1) (integerp (/ (+ p m) k)))
    (integerp (/ (- (* m m) n) k))
    (equal (- (* a a) (* n (* b b))) k)
    (implies 
        (and 
            (equal f 1) 
            (not (equal c 1))
        ) 
        (< (abs k) (abs c))
    ))
    */
   while (k != 1 || f != 1)
    {   // abkguhv
        //printf("%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d\n",
        //        a,   b,   m,   k,   i,   j,   c,   d,   e,   f,   g,   h,   l,   o,   p,   q,   r,   s,   t,   u,   v,   w,   x,   y,   z);
        if (k != 0 && c != 0)
        {
            r = m + i;
            x = r / k;
            y = k * x;
            q = r - y;

            if (q == 0) // сравнение остатка от деления m + i % k == 0, i^2 сравнимо по модулю
            { // => i - наше возможное новое число
                o = i * i;
                o = o - n; // (m_n')^2 - n
                if (o != 0)
                {
                    if (o > 0)
                    {
                        s = m;
                        if (e == 1)
                        {
                            // проверка на минимальность расстояния, сохраняем в минимум, если мы здесь, мы перешли границу
                            l = p * p;
                            l = n - l;
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
                        { // тогда мы вообще не встречали подходящих чисел меньше
                            m = i;
                        }

  //                      printf("%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d\n",a,b,m,k,i,j,c,d,e,f,g,h,l,o,p,q,r,s,t,u,v,w,x,y,z);
                        if (f == 0) // compute m1
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
                        else // compute next m
                        {
                            //if (f == 1) useless if, in this branch f always equals 1, because it's not 0
                            //{
                                j = s;
                                g = h;
                                h = a;
                                u = v;
                                v = b;
                                w = m + j;
                                c = k;
                                z = w / c;
                                a = h * z;
                                b = v * z;
                                a = a - g;
                                b = b - u;
                                k = z * w;
                                d = 2 * j;
                                d = d * z;
                                k = k - d;
                                t = j * j;
                                t = t - n;
                                t = t / c;
                                k = k + t;
                            //}
                            //else
                            //{ so it's unreachable code
                            //    a = 1;
                            //    b = 0;
                            //    c = 1;
                            //    f = 1;
                            //}    
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
                { // o == 0 => n = i^2 => тривиальный случай
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
            // trivial
            a = 1;
            b = 0;
            c = 0;
            k = 1;
            f = 1;
        }
    }
            //printf("%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d%5d\n",a,b,m,k,i,j,c,d,e,f,g,h,l,o,p,q,r,s,t,u,v,w,x,y,z);

    variables[0] = a;
    variables[1] = b;
}
/*
(= (- (* a a) (* n (* b b))) 1)
*/

//int main(int argc, char** argv) {
 //   int variables[2];
 //   int n = atoi(argv[1]);

 //   chakravala(n, variables);
    //printf("%d %d\n", variables[0], variables[1]);
 //   return 0;
//}