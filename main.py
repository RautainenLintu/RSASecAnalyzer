import time
import random
import math


# Asks for timeouts for all the methods considered
def attacks_timeout_input():
    print("Enter timeouts for each attack.")
    print("Timeout = 0 means the attack is not applied.")
    print("Enter timeout for (P-1) Pollard method:")
    time_p1t = int(input())
    print("Enter timeout for rho-Pollard method:")
    time_rho = int(input())
    print("Enter timeout for ciphertext regeneration method:")
    time_cr = int(input())
    print("Enter timeout for Wiener attack method:")
    time_w = int(input())
    print("Enter timeout for iterative factorization attack method:")
    time_fa = int(input())
    return time_p1t, time_rho, time_cr, time_w, time_fa


# Downloads factorbase from "prime.txt"
def download_factorbase(filename):
    f = open(filename)
    base = f.read().split(" ")
    intbase = []
    for i in base:
        intbase.append(int(i))
    f.close()
    return intbase


# Generates RSA keys using the list of primes
def generate_keys(primes):
    p_index = random.randint(2, len(primes) - 2)
    q_index = random.randint(2, len(primes) - 2)
    p = primes[p_index]
    q = primes[q_index]
    N = p * q
    phi = (p - 1) * (q - 1)
    e = 0
    while math.gcd(e, phi) != 1:
        e = random.randint(2, phi)
    d = pow(e, -1, phi)
    return e, N, d


# generates cipher-text for message m on key (e, N)
def encrypt_rsa(e, N, m):
    return pow(m, e, N)


# Calculates d by given e and N = p * q
def find_secret_key(e, p, q, report):
    phi = (p - 1) * (q - 1)
    report.write('phi = {0}\n'.format(phi))
    if math.gcd(phi, e) != 1:
        report.write("Incorrect (e, N) pair. Secret key d cannot be retrieved")
        return 0
    d = pow(e, -1, phi)
    return d


# Applies p-1 Pollard method
def p_minus_1_pollard(e, N, time_p1, report):
    initial_time = time.time()
    report.write("p-1 Pollard method is being applied...\n")
    factorbase = download_factorbase("primes.txt")
    report.write("Factorbase downloaded...\n")
    report.write("Stage One of p-1 Pollard method\n")
    B = random.randint(2, int(math.sqrt(N)))
    report.write('B = {0}\n'.format(B))
    m_b = 1
    for p in factorbase:
        if time.time() - initial_time >= time_p1:
            report.write("p-1 Pollard method unsuccessful due to timeout.\n")
        if p > B:
            break
        p_k = p
        while p_k < B:
            p_k *= p
        m_b *= p_k
    report.write('M(B) = {0}\n'.format(m_b))
    for a in range(2, 1000000):
        if time.time() - initial_time >= time_p1:
            report.write("p-1 Pollard method unsuccessful due to timeout.\n")
            return 0, 0, 0
        b = pow(a, m_b, N)
        q = math.gcd(b - 1, N)
        report.write('a, b, q = {0}, {1}, {2}\n'.format(a, b, q))
        if q != N and q != 1:
            p = N // q
            report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
            d = find_secret_key(e, p, q, report)
            report.write('Found d: d = {0}\n'.format(d))
            return p, q, d
        if q == N:
            continue
        if q == 1:
            break
    report.write("Stage Two of p-1 Pollard method\n")
    B1 = B
    B2 = B ** 2
    report.write('B1, B2 =  {0}, {1}\n'.format(B1, B2))
    q_vect = []
    for p in factorbase:
        if time.time() - initial_time >= time_p1:
            report.write("p-1 Pollard method unsuccessful due to timeout.\n")
            return 0, 0, 0
        if p < B1:
            continue
        if p > B2:
            break
        q_vect.append(p)
    d_vect = []
    i = 0
    while i < len(q_vect) - 2:
        if time.time() - initial_time >= time_p1:
            report.write("p-1 Pollard method unsuccessful due to timeout.\n")
            return 0, 0, 0
        d_vect.append(q_vect[i + 1] - q_vect[i])
        i += 1
    b_vect = []
    b_vect.append(pow(b, q_vect[0], N))
    for d_i in d_vect:
        b_vect.append(pow(b, d_i, N))
    c_i = b_vect[0]
    G = math.gcd(N, c_i - 1)
    report.write('c_i - 1, gcd(c_i, N) = {0}, {1}\n'.format(c_i - 1, G))
    if G != 1 and G != N:
        p = c_i - 1
        q = N // p
        report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
        d = find_secret_key(e, p, q, report)
        report.write('Found d: d = {0}\n'.format(d))
        return p, q, d
    for b_i in b_vect:
        if time.time() - initial_time >= time_p1:
            report.write("p-1 Pollard method unsuccessful due to timeout.")
            return 0, 0, 0
        c_i = (c_i * b_i) % N
        G = math.gcd(N, c_i - 1)
        report.write('c_i - 1, gcd(c_i, N) = {0}, {1}\n'.format(c_i - 1, G))
        if G != 1 and G != N:
            p = c_i - 1
            q = N // (c_i - 1)
            report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
            d = find_secret_key(e, p, q, report)
            report.write('Found d: d = {0}\n'.format(d))
            return p, q, d
    report.write("Factorization using p - 1 Pollard method was not successful")
    return 0, 0, 0


# Applies rho Pollard method
def rho_pollard(e, N, time_rho, report):
    initial_time = time.time()
    report.write("Rho Pollard method is being applied...\n")
    x_0 = random.randint(2, 100)
    report.write('x0 = {0}\n'.format(x_0))
    x_seq = []
    x_seq.append(x_0)
    i = 1
    while True:
        if time.time() - initial_time >= time_rho:
            report.write("Rho Pollard method unsuccessful due to timeout\n")
            return 0, 0, 0
        x_seq.append((x_seq[i - 1] ** 2 - 1) % N)
        if i % 2 == 0:
            report.write('i, x_2i = {0}, {1}\n'.format(i/2, x_seq[i]))
            report.write('i, x_i = {0}, {1}\n'.format(i/2, x_seq[i//2]))
            delta = abs(x_seq[i] - x_seq[i//2])
            gcd = math.gcd(N, delta)
            report.write('delta = {0}\n'.format(delta))
            report.write("\n")
            if gcd != 1 and gcd != N:
                p = gcd
                q = N // gcd
                report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
                d = find_secret_key(e, p, q, report)
                report.write('Found d: d = {0}\n'.format(d))
                return p, q, d
        i += 1


# Finds binomial coefficient C(n, k)
def coefficient_c_n_k(n, k):
    c = 1
    for i in range(n-k+1, n+1):
        c *= i
    for i in range(1, k+1):
        c //= i
    return c


# removes unused zeros for higher powers in a polynomial
def remove_excessive_zeros(f):
    zero_count = 0
    while zero_count < len(f) and f[len(f) - 1 - zero_count] == 0:
        zero_count += 1
    if zero_count == len(f):
        return [0]
    i = 1
    f.reverse()
    while i <= zero_count:
        f.remove(0)
        i += 1
    f.reverse()
    return f


# Divides two polynomials modulo N, returns quotient and remainder
def divide_polynomials(f, g, N):
    if f == [0] or g == [0]:
        return [0], [0]
    m = len(f)
    n = len(g)
    q = [0] * (m - n + 2)
    for i in range(m - n + 1):
        q[m - n - i] = (f[m - i - 1] * pow(g[n - 1], -1, N)) % N
        for j in range(n):
            f[m - n - i + j] = (f[m - n - i + j] - ((g[j] * q[m - n - i]) % N)) % N
    q = remove_excessive_zeros(q)
    r = remove_excessive_zeros(f)
    return q, r


# Finds GCD of polynomials modulo N
def polynomials_gcd(f, g, N):
    if len(g) > len(f):
        f, g = g, f
    q, r = divide_polynomials(f, g, N)
    while r != [0]:
        f, g = g, r
        q, r = divide_polynomials(f, g, N)
        if q == [0]:
            return [0]
    for i in range(len(g)):
        g[i] = (g[i] * pow(g[len(g) - 1], -1, N)) % N
    return g


# Applies ciphertext restoring attack
def ciphertext_restoring(e, N, time_cr, report):
    initial_time = time.time()
    report.write("Ciphertext restoring attack is being applied...\n")
    while True:
        if time.time() - initial_time >= time_cr:
            report.write("Ciphertext restoring attack unsuccessful due to timeout.\n")
            return 0,0,0
        a = random.randint(2, 10)
        b = random.randint(2, 10)
        report.write('a, b = {0}, {1}\n'.format(a, b))
        report.write("Choosing random message for analysis\n")
        m1 = random.randint(2, N - 1)
        report.write('m1 = {0}\n'.format(m1))
        m2 = (a * m1 + b) % N
        report.write('m2 = (a * m1 + b) mod N =  {0}\n'.format(m2))
        c1 = encrypt_rsa(e, N, m1)
        report.write('c1 = {0}\n'.format(c1))
        c2 = encrypt_rsa(e, N, m2)
        report.write('c2 = {0}\n'.format(c2))
        f = [0] * (e + 1)
        g = [0] * (e + 1)
        f[e] = 1
        f[0] = (-c1) % N
        for i in range(e + 1):
            if time.time() - initial_time >= time_cr:
                report.write("Ciphertext restoring attack unsuccessful due to timeout.\n")
                return 0, 0, 0
            g[i] = coefficient_c_n_k(e, i) % N
            g[i] = g[i] * pow(a, i, N) % N
            g[i] = g[i] * pow(b, e - i, N) % N
        g[0] = (g[0] - c2) % N
        report.write('f(x) = {0}\n'.format(f))
        report.write('g(x) = {0}\n'.format(g))
        d_x = polynomials_gcd(f, g, N)
        report.write('d(x) = {0}\n'.format(d_x))
        if d_x == [0]:
            report.write("Attack failed. Choosing another message...\n")
            continue
        k = len(d_x) - 1
        report.write('k = {0}\n'.format(k))
        d_k_1 = k * d_x[k - 1]
        report.write('d_k_1 = {0}\n'.format(d_k_1))
        if d_k_1 == 0:
            report.write("Attack failed. Choosing another message...\n")
            continue
        GCD = math.gcd(d_k_1, N)
        report.write('GCD = {0}\n'.format(GCD))
        if GCD not in [0, 1, N]:
            p = GCD
            q = N // GCD
            report.write("Factorization of N = p * q found: \n", p, q)
            d = find_secret_key(e, p, q, report)
            report.write('d = {0}\n'.format(d))
            return p, q, d
        else:
            decrypted_m1 = (N - d_k_1) % N
            if decrypted_m1 == m1:
                report.write('Attack successful. Restored message m1 = {0}\n'.format(decrypted_m1))
                return 1, 1, 1
            else:
                report.write("Attack failed. Choosing another message...\n")


# Returns a dictionary of convergent fractions
def get_convergent_fractions(numerator, denominator):
    if denominator == 0:
        return {}
    n = numerator
    d = denominator
    fraction = {-2: {"p_n": 0, "q_n": 1}, -1: {"p_n": 1, "q_n": 0}}
    i = 0
    while True:
        a_n = n // d
        fraction[i] = {"p_n": a_n * fraction[i-1]["p_n"] + fraction[i-2]["p_n"], "q_n": a_n * fraction[i - 1]["q_n"] + fraction[i - 2]["q_n"]}
        n, d = d, n % d
        if numerator  == fraction[i]["p_n"] and denominator == fraction[i]["q_n"]:
            break
        i += 1
    return fraction


# Solves X^2 - ((N - f_n + 1)* X + N = 0
def solve_equation(f_n, N):
    a = 1
    b = -(N - f_n + 1)
    c = N
    discriminant = b ** 2 - 4 * a * c
    if discriminant < 0:
        return 0, 0
    sqrt_discriminant = math.sqrt(discriminant)
    x1 = (- b + sqrt_discriminant) / (2 * a)
    x2 = (- b - sqrt_discriminant) / (2 * a)
    if x1 % 1 != 0 or x2 % 1 != 0:
        return 0, 0
    return int(x1), int(x2)


# Applies Wiener method to given public key
def wiener_attack(e, N, time_w, report):
    initial_time = time.time()
    report.write("Wiener's attack is being applied.\n")
    fractions = get_convergent_fractions(e, N)
    i = -1
    while True:
        if time.time() - initial_time >= time_w:
            report.write("Wiener's attack unsuccessful due to timeout\n")
            return 0, 0, 0
        i += 1
        if i >= len(fractions) - 2:
            report.write("Wiener's attack was not successful.\n")
            return 0, 0, 0
        k, d = fractions[i]["p_n"], fractions[i]["q_n"]
        report.write("\n")
        report.write('P_n / Q_n =  {0}/{1}\n'.format(k, d))
        if k == 0:
            report.write("k = 0. Impossible to find f_n.\n")
            continue
        f_n = (e * d - 1) / k
        report.write('f_n = {0}\n'.format(f_n))
        if f_n % 1 != 0:
            report.write("Non-integer phi(N). Switching to the next convergent fraction\n")
            continue
        p, q = solve_equation(f_n, N)
        if p == 0 and q == 0:
            report.write("Impossible to solve equation in integers. Search continues...\n")
            continue
        report.write('p, q = {0}, {1}\n'.format(p, q))
        report.write("Checking factorization...\n")
        if p * q == N and p > 0 and q > 0:
            report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
            d = find_secret_key(e, p, q, report)
            report.write('Found d: d = {0}\n'.format(d))
            return p, q, d
        else:
            report.write("Incorrect p, q. Search continues...\n")


# Applies iterative factorization attack to given public key
def iterative_factorization_attack(e, N, time_itfa, report):
    report.write("Iterative factorization attack begins.\n")
    initial_time = time.time()
    while True:
        if time.time() - initial_time > time_itfa:
            report.write("Iterative factorization attack unsuccessful due to timeout.\n")
            break
        m = random.randint(2, N - 1)
        report.write('Generated message m = {0}\n'.format(m))
        c = encrypt_rsa(e, N, m)
        report.write('Ciphertext c = {0}\n'.format(c))
        if math.gcd(N, m) > 1:
            p, q = m, N // m
            report.write('Successful factorization. (p, q) = {0}, {1}\n'.format(p, q))
            d = find_secret_key(e, p, q, report)
            report.write('Found d: d = {0}\n'.format(d))
            return p, q, d
        k = 1
        c_i = pow(c, e, N)
        while (c_i - c) % N != 0:
            if time.time() - initial_time > time_itfa:
                report.write("Iterative factorization attack unsuccessful due to timeout.\n")
                break
            c_i = pow(c_i, e, N)
            k += 1
        decrypted_m = pow(c, e ** (k - 1), N)
        if decrypted_m == m:
            report.write('Attack successful. Restored message m1 = {0}\n'.format(decrypted_m))
            return 1, 1, 1
        else:
            report.write("Attack failed. Choosing another message...\n")


while True:
    print("Choose mode 1 (analysis mode) or 2 (test mode):")
    mode = input()
    while mode != '1' and mode != '2':
        print("Incorrect mode. Try again:")
        mode = input()
    if mode == '1':
        report = open("report.txt", "w")
        report.write("Analysis begins.\n")
        print("Enter e:")
        e = int(input())
        print("Enter N:")
        N = int(input())
        report.write('Public key (e, N) = {0}, {1}\n'.format(e, N))
        report.write("")
        time_p1, time_rho, time_cr, time_w, time_itfa = attacks_timeout_input()
        report.write('p - 1 Pollard attack timeout = {0}\n'.format(time_p1))
        report.write('Rho Pollard attack timeout = {0}\n'.format(time_rho))
        report.write('Ciphertext restoring attack timeout = {0}\n'.format(time_cr))
        report.write('Wiener attack timeout = {0}\n'.format(time_w))
        report.write('Iterative factorization attack timeout = {0}\n'.format(time_itfa))
        report.write("\n")
        if time_p1 != 0:
            p_minus_1_pollard(e, N, time_p1, report)
            report.write("\n")
        if time_rho != 0:
            rho_pollard(e, N, time_rho, report)
            report.write("\n")
        if time_cr != 0:
            ciphertext_restoring(e, N, time_cr, report)
            report.write("\n")
        if time_w != 0:
            wiener_attack(e, N, time_w, report)
            report.write("\n")
        if time_itfa != 0:
            iterative_factorization_attack(e, N, time_itfa, report)
        report.close()
        print("Analysis finished. You can find your report in report.txt.")
        print()

    if mode == '2':
        time_p1, time_rho, time_cr, time_w, time_itfa = attacks_timeout_input()
        factorbase = download_factorbase("primes.txt")
        # the factorbase only continues first 1M primes. Size is restricted
        print("Enter task in bits:")
        s_bits = int(input())
        prime_floor = 2 ** (s_bits - 1)
        prime_ceil = 2 ** s_bits - 1
        while prime_ceil > factorbase[len(factorbase) - 1]:
            print("Unfortunately, the size is too large due to limited factorbase...")
            print("Try again:")
            s_bits = int(input())
            prime_floor = 2 ** (s_bits - 1)
            prime_ceil = 2 ** s_bits - 1
        print("Lowest border of p = ", prime_floor)
        print("Highest border of p = ", prime_ceil)
        suitable_primes = []
        for prime in factorbase:
            if prime < prime_floor:
                continue
            if prime > prime_ceil:
                break
            suitable_primes.append(prime)
        print("List of possible prime numbers is downloaded.")

        while True:
            report = open("report.txt", "w")
            e, N, d = generate_keys(suitable_primes)
            if time_p1 != 0:
                p, q, d_retrieved = p_minus_1_pollard(e, N, time_p1, report)
                if (p, q, d_retrieved) != (0, 0, 0):
                    print("p - 1 Pollard method successful")
                    print("Weak key generated. (e, N), d = ", e, N, d)
                    break
            if time_rho != 0:
                p, q, d_retrieved = rho_pollard(e, N, time_p1, report)
                if (p, q, d_retrieved) != (0, 0, 0):
                    print("Rho Pollard method successful")
                    print("Weak key generated. (e, N), d = ", e, N, d)
                    break
            if time_cr != 0:
                p, q, d_retrieved = ciphertext_restoring(e, N, time_p1, report)
                if (p, q, d_retrieved) != (0, 0, 0):
                    print("Ciphertext restoring method successful")
                    print("Weak key generated. (e, N), d = ", e, N, d)
                    break
            if time_w != 0:
                p, q, d_retrieved = wiener_attack(e, N, time_p1, report)
                if (p, q, d_retrieved) != (0, 0, 0):
                    print("Wiener method successful")
                    print("Weak key generated. (e, N), d = ", e, N, d)
                    break
            if time_itfa != 0:
                p, q, d_retrieved = iterative_factorization_attack(e, N, time_p1, report)
                if (p, q, d_retrieved) != (0, 0, 0):
                    print("Iterative factorization method successful")
                    print("Weak key generated. (e, N), d = ", e, N, d)
                    break
            report.close()
    print()
    print("Program finished")
    print("Press Enter to restart")
    input()
