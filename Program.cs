using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;

namespace methods5
{
    class Program
    {
        public static BigInteger p, A, NR;
        public static int w = 0;
        public static List<BigInteger> NR_;

        static BigInteger Pow(BigInteger a, BigInteger b)
        {
            BigInteger result = 1;
            for (BigInteger i = 0; i < b; i++)
                result *= a;
        
            return result;
        }
        static bool IsPrime(BigInteger p)
        {
            BigInteger rounds = 30, t = p - 1;
            if (p == 2 || p == 3)
                return true;

            if (p < 2 || p % 2 == 0)
                return false;

            int s = 0;
            while (t % 2 == 0)
            {
                t /= 2;
                s += 1;
            }

            for (int i = 0; i < rounds; i++)
            {
                RNGCryptoServiceProvider rng = new RNGCryptoServiceProvider();
                byte[] _a = new byte[p.ToByteArray().LongLength];
                BigInteger a;
                do
                {
                    rng.GetBytes(_a);
                    a = new BigInteger(_a);
                }
                while (a < 2 || a >= p - 2);

                BigInteger x = BigInteger.ModPow(a, t, p);
                if (x == 1 || x == p - 1)
                    continue;

                for (int r = 1; r < s; r++)
                {
                    x = BigInteger.ModPow(x, 2, p);

                    if (x == 1)
                        return false;

                    if (x == p - 1)
                        break;
                }

                if (x != p - 1)
                    return false;
            }
            return true;
        }
        static BigInteger GenerateNumberOfLength(int l)
        {
            RNGCryptoServiceProvider rng = new RNGCryptoServiceProvider();
            byte[] _result = new byte[BigInteger.Pow(2, l).ToByteArray().LongLength];
            BigInteger result;
            do
            {
                rng.GetBytes(_result);
                result = new BigInteger(_result);
            } while (result <= BigInteger.Pow(2, (l - 1)) || result >= BigInteger.Pow(2, l));
            
            return result;
        }
        static BigInteger GenerateSimpleNumberOfLength(int l)
        {   
            BigInteger result;
            result = GenerateNumberOfLength(l);
            while (!IsPrime(result))
            {   
                result = GenerateNumberOfLength(l);
            }
            return result;
        }
        private static void FindPrimeNumberOfLength(int l)
        {
            do
            {
                p = GenerateSimpleNumberOfLength(l);
            } while ((p % 4) != 1);
        }
        private static Boolean CheckSqrt(BigInteger n, BigInteger root)
        {
            BigInteger lowerBound = root * root, upperBound = (root + 1) * (root + 1);

            return (n >= lowerBound && n < upperBound);
        }
        public static BigInteger Sqrt_N(BigInteger N)
        {
            if (N == 0) 
                return 0;

            if (N > 0)
            {
                int bitLength = Convert.ToInt32(Math.Ceiling(BigInteger.Log(N, 2)));
                BigInteger root = BigInteger.One << (bitLength / 2);

                while (!CheckSqrt(N, root))
                {
                    root += N / root;
                    root /= 2;
                }
                return root;
            }
            throw new ArithmeticException("NaN");
        }
        static BigInteger BinaryEuclide(BigInteger a, BigInteger b)
        {
            BigInteger g = 1;
            while (a % 2 == 0 && b % 2 == 0)
            {
                a = a / 2;
                b = b / 2;
                g = 2 * g;
            }
            BigInteger u = a, v = b;
            while (u != 0)
            {
                while (u % 2 == 0) 
                    u = u / 2;
                while (v % 2 == 0) 
                    v = v / 2;
                if (u >= v) 
                    u = u - v;
                else 
                    v = v - u;
            }
            return g * v;
        }
        static Tuple<BigInteger,BigInteger> ExtendedEuclide(BigInteger a, BigInteger b)
        {
            BigInteger r0 = a, r1 = b, x0 = 1, x1 = 0, y0 = 0, y1 = 1, x, y, d;
            while (true)
            {
                BigInteger q = r0 / r1, r = r0 % r1;
                if (r == 0) 
                    break;
                else
                {
                    r0 = r1;
                    r1 = r;
                    x = x0 - q * x1;
                    x0 = x1;
                    x1 = x;
                    y = y0 - q * y1;
                    y0 = y1;
                    y1 = y;
                }
            }
            d = r1;
            x = x1;
            y = y1;
            return new Tuple<BigInteger,BigInteger>(x, y);
        }
        public static int Legendre(BigInteger a, BigInteger p)
        {
            if (p < 2) 
                Console.WriteLine("Ошибка. P должно быть больше 2");
            if (a == 0)
                return 0;
            
            if (a == 1)
                return 1;
            
            int result;
            if (a < 0)
            {
                result = Legendre(-a, p);
                BigInteger deg = (p - 1) / 2;
                if (deg % 2 != 0) result = -result;
            }
            else
            {
                if (a % 2 == 0)
                {
                    result = Legendre(a / 2, p);
                    BigInteger deg = (p * p - 1) / 8;
                    if (deg % 2 != 0) 
                        result = -result;
                }
                else
                {
                    result = Legendre(p % a, a);
                    BigInteger deg = (a - 1) * ((p - 1) / (4));
                    if (deg % 2 != 0) 
                        result = -result;
                }
            }
            return result;
        }
        static BigInteger Jacobi(BigInteger a, BigInteger n)
        {
            if (BinaryEuclide(a, n) != 1)
                return 0;
            
            BigInteger r = 1;
            if (a < 0)
            {
                a = -a;
                if (n % 4 == 3)
                    r = -r;
            }
            while (a != 0)
            {
                BigInteger k = 0;
                while (a % 2 == 0)
                {
                    k++;
                    a = a / 2;
                }
                if (k % 2 != 0)
                {
                    if (n % 8 == 3 || n % 8 == 5)
                        r = -r;
                }
                if (n % 4 == 3 && a % 4 == 3)
                    r = -r;
                
                BigInteger temp = a;
                a = n % a;
                n = temp;
            }
            return r;
        }
        static List<BigInteger> ComparisonSolution(BigInteger a, BigInteger b, BigInteger m)
        {
            List<BigInteger> answer = new List<BigInteger>();
            BigInteger d = BinaryEuclide(a, m);
            if (b % d != 0)
                return answer;
            else
            {
                BigInteger a1 = a / d, b1 = b / d, m1 = m / d;
                Tuple<BigInteger, BigInteger> xy = ExtendedEuclide(a1, m1);
                BigInteger x0 = (b1 * xy.Item1) % m1;
                while (x0 < 0) 
                    x0 = x0 + m1;
                answer.Add(x0 % m1);
            }
            return answer;
        }
        static BigInteger ReverseElement(BigInteger a, BigInteger m)
        {
            BigInteger d = BinaryEuclide(a, m);
            if (d != 1)
                return -1;
            else
            {
                List<BigInteger> answer = ComparisonSolution(a, 1, m);
                return answer[0];
            }
        }
        static BigInteger SqrtMod(BigInteger a, BigInteger p)
        {
            a += p;
            BigInteger jacobi = Jacobi(a, p);
            if (jacobi == -1)
                return 0;
            
            int N = 0;
            if (jacobi == 1)
            {
                for (int i = 2; i < p; i++)
                {
                    if (Jacobi(i, p) == -1)
                    {
                        N = i;
                        break; 
                    }
                }
            }
            BigInteger h = p - 1;
            int k = 0;
            while (h % 2 == 0)
            {
                k++;
                h = h / 2;
            }
            BigInteger a1 = (int)BigInteger.ModPow(a, (h + 1) / 2, p);
            BigInteger a2 = ReverseElement(a, p);
            BigInteger N1 = BigInteger.ModPow(N, h, p);
            BigInteger N2 = 1;
            BigInteger[] j = new BigInteger[k - 1];
            for (int i = 0; i <= k - 2; i++)
            {
                BigInteger b = (a1 * N2) % p;
                BigInteger c = (a2 * b * b) % p;
                BigInteger pow = Pow(2, k - 2 - i);
                BigInteger d = BigInteger.ModPow(c, pow, p);
                if (d == 1)
                    j[i] = 0;
                
                if (d == p - 1 || d - p == -1)
                    j[i] = 1;
                
                N2 = (N2 * (BigInteger.ModPow(N1, BigInteger.Pow(2, i) * j[i], p))) % p;
            }
            BigInteger answer = (a1 * N2) % p;
            BigInteger answer1 = (-answer + p) % p;
            return answer;
        }
        public static List<BigInteger> Decomposition_P(BigInteger D, BigInteger p)
        {
            if (Legendre(-D, p) == -1) 
                return new List<BigInteger>();
            BigInteger R = SqrtMod(-D, p);
            int i = 0;
            List<BigInteger> U = new List<BigInteger>();
            List<BigInteger> M = new List<BigInteger>();
            U.Add(R);
            M.Add(p);
            do
            {
                M.Add((U[i] * U[i] + D) / M[i]);
                U.Add(BigInteger.Min(U[i] % M[i + 1], M[i + 1] - U[i] % M[i + 1]));
                i++;
            } while (M[i] != 1);
            i--;
            List<BigInteger> a = new List<BigInteger>();
            List<BigInteger> b = new List<BigInteger>();
            for (int j = 0; j <= i; j++)
            {
                a.Add(0);
                b.Add(0);
            }
            a[i] = U[i];
            b[i] = 1;
            while (i != 0)
            {
                BigInteger znamenatel = a[i] * a[i] + D * b[i] * b[i];
                if ((U[i - 1] * a[i] + D * b[i]) % znamenatel == 0)
                    a[i - 1] = (U[i - 1] * a[i] + D * b[i]) / znamenatel;
                else
                    a[i - 1] = (-U[i - 1] * a[i] + D * b[i]) / znamenatel;
                
                if ((-a[i] + U[i - 1] * b[i]) % znamenatel == 0)
                    b[i - 1] = (-a[i] + U[i - 1] * b[i]) / znamenatel;
                else
                    b[i - 1] = (-a[i] - U[i - 1] * b[i]) / znamenatel;
                
                i--;
            }
            List<BigInteger> answer = new List<BigInteger>();
            answer.Add(a[0]);
            answer.Add(b[0]);
            return answer;
        }
        public static bool CheckQuadraticResidue(BigInteger A, BigInteger p) => 
        BigInteger.ModPow(A, (p - 1) / 2, p) == 1;
        private static void CheckA(ref bool t, ref BigInteger k, int n)
        {
            if (NR_[0] == NR_[1] * n)
            {
                for (BigInteger i = k; ; i++)
                {
                    if (i > 1000000)
                    {
                        t = false;
                        break;
                    }
                    bool flag = CheckQuadraticResidue((i + 1) % p, NR_[0]);
                    if (n == 4 && flag || n == 2 && !flag)
                    {
                        A = i;
                        k = A + 1;
                        break;
                    }
                }
            }
        }
        private static List<BigInteger> NR_function(BigInteger a, BigInteger b, BigInteger p)
        {
            List<BigInteger> T = new List<BigInteger>();
            T.Add(b * (-2));
            T.Add(a * 2);
            T.Add(b * 2);
            T.Add(a * (-2));
            for (int i = 0; i < T.Count; i++)
            {
                T[i] += (1 + p);

                if ((T[i] % 2).Equals(0) && IsPrime((T[i] / 2)))
                    return new List<BigInteger>() {T[i],T[i] / 2};
                else 
                    if ((T[i] % 4).Equals(0) && IsPrime((T[i] / 4)))
                        return new List<BigInteger>() {T[i],T[i] / 4};
            }
            return new List<BigInteger>();
        }
         public static List<BigInteger> SumPoints(List<BigInteger> P1, List<BigInteger> P2, BigInteger A, BigInteger p)
        {
            List<BigInteger> answer = new List<BigInteger>();
            BigInteger x1 = P1[0],y1 = P1[1], x2 = P2[0], y2 = P2[1], alpha;
            if (x1 == x2 && y1 == y2)
            {
                BigInteger numerator = (3 * x1 * x1 + A) % p, denomerator = (2 * y1) % p;
                if (denomerator == 0) 
                    return answer;
                alpha = numerator * ReverseElement(denomerator, p) % p;
            }
            else
            {
                BigInteger numerator = (y2 - y1) % p, denomerator = (x2 - x1) % p;
                denomerator = denomerator >= 0 ? denomerator : denomerator + p;
                if (denomerator == 0) 
                    return answer;
                alpha = numerator * ReverseElement(denomerator, p) % p;
            }
            BigInteger xr = (alpha * alpha - x1 - x2) % p, yr = (-y1 + alpha * (x1 - xr)) % p;
            xr = xr >= 0 ? xr : xr + p;
            yr = yr >= 0 ? yr : yr + p;
            answer.Add(xr);
            answer.Add(yr);
            return answer;
        }
        static void Main(string[] args)
        {
            int m = 5;
            BigInteger D = 1;
            bool t = true;
            Console.Write("Введите длину характеристики поля l = ");
            int l = int.Parse(Console.ReadLine());
            if (l <= 4)
            {
                Console.WriteLine("Длина характеристики поля <= 4. Введите корректную длину!");
                return;
            }
            
            while (true)
            {
                step1: while (true)
                {
                    t = true;
                    List<BigInteger> decomposition;
                    FindPrimeNumberOfLength(l);
                    decomposition = Decomposition_P(D, p);

                    NR_ = NR_function(decomposition[0], decomposition[1], p);

                    if (!NR_.Any()) 
                        goto step1;

                    if (p != NR_[1])
                    {
                        for (int i = 1; i <= m; i++)
                        {
                            if (BigInteger.ModPow(p, i, NR_[1]) == 0)
                            {
                                w = w + 1;
                                if (w > 10)
                                {
                                    Console.WriteLine("Нет p, удовлятворяющего всем условиям");
                                    return;
                                }
                                goto step1;
                            }
                        }
                        break;
                    }
                    goto step1;
                }
            int j = 1;
            BigInteger k = 2, counter = 0;
            List<BigInteger> x0y0 = new List<BigInteger>();
        
            step5: while (true)
            {
                    if (NR_[0] == NR_[1] * 2)
                        CheckA(ref t, ref k, 2);
                    else
                        CheckA(ref t, ref k, 4);
                    
                    if (!t) 
                        goto step6;
                    x0y0 = new List<BigInteger>();
                    for (int i = j; ; i++, j++)
                    {
                        BigInteger z = (A * i + i * i * i) % p;
                        if (Legendre(z, p) == 1)
                        {
                            if (Sqrt_N(z) == 0) 
                                continue;
                            else
                            {
                                x0y0.Add(i);
                                x0y0.Add(Sqrt_N(z));
                            }
                            i++;
                            j++;
                            break;
                        }
                    }
                    BigInteger cnt = NR_[0];
                    List<BigInteger> Nx0y0 = new List<BigInteger>();
                    while (cnt != 0)
                    {
                        if (!Nx0y0.Any()) 
                            Nx0y0 = x0y0;
                        else 
                            Nx0y0 = SumPoints(Nx0y0, x0y0, A, p);
                        cnt--;
                    }
            
                    if (Nx0y0.Any())
                    {
                        if (counter++ < 10)
                            goto step5;
                        else
                            goto step1;      
                    }
                    break;
            }
                
            step6:  if (!t) 
                        continue;
                NR = NR_[0] / NR_[1];
                List<BigInteger> NRx0y0 = new List<BigInteger>();
                List<BigInteger> Q = new List<BigInteger>();
                if (NR != 0)
                {
                    while (NR != 0)
                    {
                        if (!NRx0y0.Any()) 
                            NRx0y0 = x0y0;
                        else 
                            NRx0y0 = SumPoints(NRx0y0, x0y0, A, p);
                        NR--;
                    }
                    Q = NRx0y0;
                }       
            
                if (!Q.Any()) 
                    continue;
                
                WriteToFiles(Q);
                Console.WriteLine("Результат:");
                Console.WriteLine("p = " + p);
                Console.WriteLine("A = " + A);
                Console.WriteLine("r = " + NR_[1]);
                Console.WriteLine("Q = (" + Q[0] + ", " + Q[1] + ")");
                break;
            }
            Console.Read();
        }
        private static void WriteToFiles(List <BigInteger> Q)
        {
            StreamWriter Out = null, Out1 = null;
            try
            {
                Out = new StreamWriter(File.Open("x.txt", FileMode.Create));
                Out1 = new StreamWriter(File.Open("y.txt", FileMode.Create));
            }
            catch (IOException e)
            {
                Console.WriteLine(e.Message);
            }
            BigInteger count = NR_[1];
            List <BigInteger> xy = new List<BigInteger>();
            while (count != 1)
            {
                if (!xy.Any())
                {
                    xy = Q;
                    try
                    {
                        Out.WriteLine(xy[0]);
                        Out1.WriteLine(xy[1]);
                    }
                    catch (IOException e)
                    {
                        Console.WriteLine(e.Message);
                    }
                }
                else
                {
                    xy = SumPoints(xy, Q, A, p);
                    try
                    {
                        Out.WriteLine(xy[0]);
                        Out1.WriteLine(xy[1]);
                    }
                    catch (IOException e)
                    {
                        Console.WriteLine(e.Message);
                    }
                }
                count--;
            }
            Out.Close();
            Out1.Close();
        }
    }
}
