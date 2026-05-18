print = print
import math
import random
import base64
import struct
import string as _string
import os
import hashlib

ABECEDARIO = {
    'a': 1,  'b': 2,  'c': 3,  'd': 4,  'e': 5,
    'f': 6,  'g': 7,  'h': 8,  'i': 9,  'j': 10,
    'k': 11, 'l': 12, 'm': 13, 'n': 14, 'o': 15,
    'p': 16, 'q': 17, 'r': 18, 's': 19, 't': 20,
    'u': 21, 'v': 22, 'w': 23, 'x': 24, 'y': 25,
    'z': 26
}

NUMERO_A_LETRA = {v: k for k, v in ABECEDARIO.items()}

MARCADOR_DIGITO = -1
OFFSET_DIGITO = 27


# ──────────────────────────────────────────────
# SEEDS ALEATORIAS
# ──────────────────────────────────────────────

def generar_seed_random():
    """Genera una seed aleatoria de 8 caracteres."""
    caracteres = _string.ascii_lowercase + _string.digits
    return "".join(random.choice(caracteres) for _ in range(8))


def pedir_seed(prompt="Seed para el abecedario (vacío = normal, 'random' = aleatoria): "):
    """
    Pide una seed al usuario.
    Si escribe 'random', genera una aleatoria y la muestra.
    """
    seed = input(prompt).strip()
    if seed.lower() == "random":
        seed = generar_seed_random()
        print(f"✓ Seed aleatoria generada: {seed}")
    return seed


# ──────────────────────────────────────────────
# GENERACIÓN DE CLAVES RSA
# ──────────────────────────────────────────────

def es_primo_miller_rabin(n, k=20):
    if n < 2:
        return False

    if n == 2 or n == 3:
        return True

    if n % 2 == 0:
        return False

    r, d = 0, n - 1

    while d % 2 == 0:
        r += 1
        d //= 2

    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)

        if x == 1 or x == n - 1:
            continue

        for _ in range(r - 1):
            x = pow(x, 2, n)

            if x == n - 1:
                break
        else:
            return False

    return True


def primo_aleatorio(bits):
    while True:
        n = random.getrandbits(bits)
        n |= (1 << (bits - 1))
        n |= 1

        if es_primo_miller_rabin(n):
            return n


def cifras_a_bits(cifras):
    return math.ceil(cifras * math.log2(10))


# ──────────────────────────────────────────────
# CODIFICACIÓN DER / PEM
# ──────────────────────────────────────────────

def encode_der_integer(n):
    length = max(1, (n.bit_length() + 7) // 8)
    raw = n.to_bytes(length, byteorder='big')

    if raw[0] & 0x80:
        raw = b'\x00' + raw

    return encode_der_tlv(0x02, raw)


def encode_der_tlv(tag, value):
    length = len(value)

    if length < 0x80:
        len_bytes = bytes([length])

    elif length < 0x100:
        len_bytes = bytes([0x81, length])

    elif length < 0x10000:
        len_bytes = bytes([0x82, length >> 8, length & 0xFF])

    else:
        raise ValueError("Longitud demasiado grande")

    return bytes([tag]) + len_bytes + value


def generar_clave_publica_pem(n, e):
    seq = encode_der_integer(n) + encode_der_integer(e)
    der = encode_der_tlv(0x30, seq)
    b64 = base64.encodebytes(der).decode('ascii')

    return (
        "-----BEGIN RSA PUBLIC KEY-----\n"
        + b64
        + "-----END RSA PUBLIC KEY-----"
    )


def generar_clave_privada_pem(n, e, d, p, q):
    dp = d % (p - 1)
    dq = d % (q - 1)
    qInv = pow(q, -1, p)

    seq = (
        encode_der_integer(0)
        + encode_der_integer(n)
        + encode_der_integer(e)
        + encode_der_integer(d)
        + encode_der_integer(p)
        + encode_der_integer(q)
        + encode_der_integer(dp)
        + encode_der_integer(dq)
        + encode_der_integer(qInv)
    )

    der = encode_der_tlv(0x30, seq)
    b64 = base64.encodebytes(der).decode('ascii')

    return (
        "-----BEGIN RSA PRIVATE KEY-----\n"
        + b64
        + "-----END RSA PRIVATE KEY-----"
    )


# ──────────────────────────────────────────────
# DECODIFICACIÓN DER
# ──────────────────────────────────────────────

def decode_der_tlv(data, offset=0):
    tag = data[offset]
    offset += 1

    length_byte = data[offset]
    offset += 1

    if length_byte < 0x80:
        length = length_byte

    elif length_byte == 0x81:
        length = data[offset]
        offset += 1

    elif length_byte == 0x82:
        length = (data[offset] << 8) | data[offset + 1]
        offset += 2

    else:
        raise ValueError("Longitud DER no soportada")

    value = data[offset:offset + length]

    return tag, value, offset + length


def decode_der_integer(value_bytes):
    return int.from_bytes(value_bytes, byteorder='big')


def pem_a_der(pem_text):
    lines = pem_text.strip().splitlines()
    b64_lines = [l for l in lines if not l.startswith('-----')]

    return base64.b64decode(''.join(b64_lines))


def parsear_clave_publica_pem(pem_text):
    der = pem_a_der(pem_text)

    tag, seq_val, _ = decode_der_tlv(der, 0)

    if tag != 0x30:
        raise ValueError("Se esperaba SEQUENCE")

    offset = 0

    tag, n_bytes, offset = decode_der_tlv(seq_val, offset)
    n = decode_der_integer(n_bytes)

    tag, e_bytes, offset = decode_der_tlv(seq_val, offset)
    e = decode_der_integer(e_bytes)

    return n, e


def parsear_clave_privada_pem(pem_text):
    der = pem_a_der(pem_text)

    tag, seq_val, _ = decode_der_tlv(der, 0)

    if tag != 0x30:
        raise ValueError("Se esperaba SEQUENCE")

    offset = 0

    tag, ver_bytes, offset = decode_der_tlv(seq_val, offset)

    tag, n_bytes, offset = decode_der_tlv(seq_val, offset)
    n = decode_der_integer(n_bytes)

    tag, e_bytes, offset = decode_der_tlv(seq_val, offset)
    e = decode_der_integer(e_bytes)

    tag, d_bytes, offset = decode_der_tlv(seq_val, offset)
    d = decode_der_integer(d_bytes)

    tag, p_bytes, offset = decode_der_tlv(seq_val, offset)
    p = decode_der_integer(p_bytes)

    tag, q_bytes, offset = decode_der_tlv(seq_val, offset)
    q = decode_der_integer(q_bytes)

    return n, e, d, p, q


# ──────────────────────────────────────────────
# MENSAJE CIFRADO PEM
# ──────────────────────────────────────────────

def numeros_a_pem_mensaje(numeros_cifrados):
    partes = []

    for num in numeros_cifrados:
        es_negativo = num < 0
        abs_val = abs(num)

        if abs_val == 0:
            num_bytes = b'\x00'

        else:
            longitud = (abs_val.bit_length() + 7) // 8
            num_bytes = abs_val.to_bytes(longitud, byteorder='big')

        signo = b'\x01' if es_negativo else b'\x00'
        lon = len(num_bytes).to_bytes(4, byteorder='big')

        partes.append(signo + lon + num_bytes)

    datos = b''.join(partes)

    b64 = base64.encodebytes(datos).decode('ascii')

    return (
        "-----BEGIN RSA ENCRYPTED MESSAGE-----\n"
        + b64
        + "-----END RSA ENCRYPTED MESSAGE-----"
    )


def pem_mensaje_a_numeros(pem_text):
    datos = pem_a_der(pem_text)

    numeros = []

    i = 0

    while i < len(datos):
        signo = datos[i]
        i += 1

        longitud = int.from_bytes(datos[i:i + 4], byteorder='big')
        i += 4

        num_bytes = datos[i:i + longitud]
        i += longitud

        valor = int.from_bytes(num_bytes, byteorder='big')

        if signo == 1:
            valor = -valor

        numeros.append(valor)

    return numeros


# ──────────────────────────────────────────────
# DETECCIÓN DE CONTENIDO CIFRADO
# ──────────────────────────────────────────────

def detectar_mensaje_cifrado(contenido):
    """
    Detecta si el contenido tiene un mensaje cifrado.
    Retorna: (tipo, datos)
    - tipo: 'pem_mensaje', 'numeros', None
    - datos: el PEM extraído, los números como lista, o None
    """
    contenido = contenido.strip()

    # Buscar PEM de mensaje cifrado
    if "-----BEGIN RSA ENCRYPTED MESSAGE-----" in contenido:
        inicio = contenido.find("-----BEGIN RSA ENCRYPTED MESSAGE-----")
        fin = contenido.find("-----END RSA ENCRYPTED MESSAGE-----")
        if fin != -1:
            pem = contenido[inicio:fin + len("-----END RSA ENCRYPTED MESSAGE-----")]
            return ('pem_mensaje', pem)

    # Buscar línea de números cifrados (patrón: números separados por espacios)
    lineas = contenido.splitlines()
    for linea in lineas:
        linea = linea.strip()
        # Ignorar líneas vacías o que parecen etiquetas
        if not linea or linea.startswith("─") or linea.startswith("=") or ":" in linea:
            continue
        # Verificar si es una secuencia de números
        partes = linea.split()
        if len(partes) >= 2:
            try:
                numeros = [int(p) for p in partes]
                # Verificar que al menos algunos números son grandes (típico de RSA)
                if any(abs(n) > 100 for n in numeros):
                    return ('numeros', numeros)
            except ValueError:
                continue

    return (None, None)


def detectar_claves_en_txt(contenido):
    claves = {}

    patrones = {
        'n': r'n\s*=\s*(\d+)',
        'e': r'e\s*=\s*(\d+)',
        'd': r'd\s*=\s*(\d+)',
        'p': r'p\s*=\s*(\d+)',
        'q': r'q\s*=\s*(\d+)',
        'phi': r'φ\(n\)\s*=\s*(\d+)',
    }

    import re

    for clave, patron in patrones.items():

        match = re.search(patron, contenido)

        if match:
            claves[clave] = int(match.group(1))

    match_seed = re.search(r'Seed\s*:\s*(.+)', contenido)

    if match_seed:
        claves['seed'] = match_seed.group(1).strip()

    match_modo = re.search(r'cifrado con\s*:\s*([ed])', contenido, re.IGNORECASE)
    if match_modo:
        claves['modo_cifrado'] = match_modo.group(1).lower()

    # Detectar PEM pública
    if "-----BEGIN RSA PUBLIC KEY-----" in contenido:
        try:
            inicio = contenido.find(
                "-----BEGIN RSA PUBLIC KEY-----"
            )

            fin = contenido.find(
                "-----END RSA PUBLIC KEY-----"
            )

            if fin != -1:

                pem = contenido[
                    inicio:
                    fin + len("-----END RSA PUBLIC KEY-----")
                ]

                n_pem, e_pem = parsear_clave_publica_pem(pem)

                claves['n'] = n_pem
                claves['e'] = e_pem
                claves['pem_publica'] = pem

        except:
            pass

    # Detectar PEM privada
    if "-----BEGIN RSA PRIVATE KEY-----" in contenido:
        try:

            inicio = contenido.find(
                "-----BEGIN RSA PRIVATE KEY-----"
            )

            fin = contenido.find(
                "-----END RSA PRIVATE KEY-----"
            )

            if fin != -1:

                pem = contenido[
                    inicio:
                    fin + len("-----END RSA PRIVATE KEY-----")
                ]

                n, e, d, p, q = parsear_clave_privada_pem(pem)

                claves['n'] = n
                claves['e'] = e
                claves['d'] = d
                claves['p'] = p
                claves['q'] = q
                claves['pem_privada'] = pem

        except:
            pass

    return claves


# ──────────────────────────────────────────────def herramientas_pem_descifrar():    print()    print("Descifrar PEM")    print("─" * 40)    print("1 → PEM clave pública → claves")    print("2 → PEM clave privada → claves")    print("3 → PEM mensaje cifrado RSA → números")    print()    opcion = input("Elige opción: ").strip()    if opcion == "1":        pem = leer_bloque_pem()        try:            n, e = parsear_clave_publica_pem(pem)            print()            print(f"n = {n}")            print(f"e = {e}")        except Exception as ex:            print(f"✗ Error: {ex}")    elif opcion == "2":        pem = leer_bloque_pem()        try:            n, e, d, p, q = parsear_clave_privada_pem(pem)            print()            print(f"n = {n}")            print(f"e = {e}")            print(f"d = {d}")            print(f"p = {p}")            print(f"q = {q}")        except Exception as ex:            print(f"✗ Error: {ex}")    elif opcion == "3":        pem = leer_bloque_pem()        try:            numeros = pem_mensaje_a_numeros(pem)            print()            print(" ".join(map(str, numeros)))        except Exception as ex:            print(f"✗ Error: {ex}")    else:        print("Opción inválida")def herramientas_pem():    print()    print("Herramientas PEM")    print("─" * 40)    print("1 → Cifrar a PEM")    print("2 → Descifrar PEM")    print()    opcion = input("Elige opción: ").strip()    if opcion == "1":        herramientas_pem_cifrar()    elif opcion == "2":        herramientas_pem_descifrar()    else:        print("Opción inválida")
# ──────────────────────────────────────────────
# SEEDS
# ──────────────────────────────────────────────

def generar_abecedario_con_seed(seed):
    letras = list("abcdefghijklmnopqrstuvwxyz")

    try:
        numeros = list(map(int, seed.split("-")))

        if len(numeros) == 26:
            return dict(zip(letras, numeros))

    except ValueError:
        pass

    numeros = list(range(1, 27))

    random.seed(seed)
    random.shuffle(numeros)

    return dict(zip(letras, numeros))


def crear_seed_personalizada():
    letras = list("abcdefghijklmnopqrstuvwxyz")

    asignaciones = {l: i + 1 for i, l in enumerate(letras)}

    print()
    print("Introduce intercambios.")
    print("Ejemplo: a c")
    print("Escribe 'listo' para terminar.")

    while True:
        entrada = input("\nIntercambio: ").strip().lower()

        if entrada == "listo":
            break

        partes = entrada.split()

        if len(partes) != 2:
            print("✗ Error")
            continue

        l1, l2 = partes

        if l1 not in asignaciones or l2 not in asignaciones:
            print("✗ Letras inválidas")
            continue

        asignaciones[l1], asignaciones[l2] = (
            asignaciones[l2],
            asignaciones[l1]
        )

        print(f"✓ {l1} ↔ {l2}")

    seed = "-".join(str(asignaciones[l]) for l in letras)

    print()
    print("Seed generada:")
    print(seed)


def buscar_seed_string():
    print()
    print("Buscador de seeds")
    print("─" * 40)

    condiciones = {}

    while True:
        letra = input("Letra (ENTER = terminar): ").strip().lower()

        if letra == "":
            break

        if letra not in _string.ascii_lowercase:
            print("✗ Letra inválida")
            continue

        try:
            numero = int(input(f"Número para '{letra}': "))

        except ValueError:
            print("✗ Número inválido")
            continue

        condiciones[letra] = numero

    longitud = int(input("Longitud de seed: "))

    letras_seed = _string.ascii_lowercase

    intentos = 0

    print()
    print("Buscando...")

    while True:
        seed = "".join(
            random.choice(letras_seed)
            for _ in range(longitud)
        )

        abecedario = generar_abecedario_con_seed(seed)

        cumple = all(
            abecedario[l] == num
            for l, num in condiciones.items()
        )

        if cumple:
            print()
            print("✓ SEED ENCONTRADA")
            print(seed)
            break

        intentos += 1

        if intentos % 10000 == 0:
            print(f"Intentos: {intentos}")


# ──────────────────────────────────────────────
# TEXTO
# ──────────────────────────────────────────────

def mostrar_abecedario():
    print()

    for letra, numero in ABECEDARIO.items():
        print(f"{letra} = {numero}")

    print()


def texto_a_numeros(texto):
    numeros = []

    for ch in texto:
        if ch == " ":
            numeros.append(0)

        elif ch.lower() in ABECEDARIO:
            numeros.append(ABECEDARIO[ch.lower()])

        elif ch.isdigit():
            numeros.append(MARCADOR_DIGITO)
            numeros.append(OFFSET_DIGITO + int(ch))

    return numeros


def numeros_a_texto(numeros):
    resultado = []

    i = 0

    while i < len(numeros):
        v = numeros[i]

        if v == 0:
            resultado.append(" ")

        elif v == MARCADOR_DIGITO:
            i += 1

            if i < len(numeros):
                digito = numeros[i] - OFFSET_DIGITO

                if 0 <= digito <= 9:
                    resultado.append(str(digito))

        elif v in NUMERO_A_LETRA:
            resultado.append(NUMERO_A_LETRA[v])

        else:
            resultado.append(f"[{v}]")

        i += 1

    return "".join(resultado)


# ──────────────────────────────────────────────
# RSA
# ──────────────────────────────────────────────

def obtener_claves_publicas():
    preguntar = input("¿Tienes n y e? (y/n): ")

    d = None

    if preguntar.lower() in ("si", "y", ""):
        n = int(input("n: "))
        e = int(input("e: "))

    else:
        p = int(input("p: "))
        q = int(input("q: "))

        n = p * q
        r = (p - 1) * (q - 1)

        print(f"n = {n}")
        print(f"φ(n) = {r}")

        e = int(input("e: "))

        d = pow(e, -1, r)

        print(f"d = {d}")

    return n, e, d


def elegir_modo_rsa():
    print()
    print("1 → usar e")
    print("2 → usar d")
    print()

    opcion = input("Elige modo: ").strip()

    return "d" if opcion == "2" else "e"


def cifrar_numero():
    numero = int(input("Número: "))

    n, e, d = obtener_claves_publicas()

    modo = elegir_modo_rsa()

    if modo == "e":
        exponente = e

    else:
        if d is None:
            d = int(input("d: "))

        exponente = d

    cifrado = pow(numero, exponente, n)

    print()
    print(cifrado)


def descifrar_numero():
    numero = int(input("Número: "))
    n = int(input("n: "))

    modo = elegir_modo_rsa()

    if modo == "e":
        d = int(input("d: "))
        resultado = pow(numero, d, n)

    else:
        e = int(input("e: "))
        resultado = pow(numero, e, n)

    print()
    print(resultado)


def cifrar_texto():
    texto = input("Texto: ")

    n, e, d = obtener_claves_publicas()

    modo = elegir_modo_rsa()

    if modo == "e":
        exponente = e

    else:
        if d is None:
            d = int(input("d: "))

        exponente = d

    numeros = texto_a_numeros(texto)

    cifrados = []

    for v in numeros:
        if v == MARCADOR_DIGITO:
            cifrados.append(-pow(abs(v), exponente, n))

        elif v == 0:
            cifrados.append(0)

        else:
            cifrados.append(pow(v, exponente, n))

    print()
    print(" ".join(map(str, cifrados)))


def descifrar_texto():
    entrada = input("Números cifrados: ")

    cifrados = list(map(int, entrada.split()))

    n = int(input("n: "))

    modo = elegir_modo_rsa()

    descifrados = []

    if modo == "e":
        d = int(input("d: "))

        for c in cifrados:
            if c < 0:
                descifrados.append(MARCADOR_DIGITO)

            elif c == 0:
                descifrados.append(0)

            else:
                descifrados.append(pow(c, d, n))

    else:
        e = int(input("e: "))

        for c in cifrados:
            if c < 0:
                descifrados.append(MARCADOR_DIGITO)

            elif c == 0:
                descifrados.append(0)

            else:
                descifrados.append(pow(c, e, n))

    texto = numeros_a_texto(descifrados)

    print()
    print(texto)


# ──────────────────────────────────────────────
# CIFRAR/DESCIFRAR DESDE FICHERO TXT
# ──────────────────────────────────────────────

def cifrar_desde_txt():
    print()
    print("Cifrar desde fichero TXT")
    print("─" * 40)

    ruta = input(
        "Ruta del fichero (o nombre si está en la misma carpeta): "
    ).strip()

    if not os.path.exists(ruta):
        print(f"✗ No se encontró el fichero: {ruta}")
        return

    with open(ruta, 'r', encoding='utf-8') as f:
        contenido = f.read()

    claves = detectar_claves_en_txt(contenido)

    print()

    if claves:
        print("Claves detectadas en el fichero:")

        for k, v in claves.items():
            if k != 'seed':
                print(f"  {k} = {v}")
            else:
                print(f"  seed = {v}")

    print()

    mensaje = input("Mensaje a cifrar: ").strip()

    if not mensaje:
        print("✗ No se proporcionó mensaje")
        return

    if 'n' in claves and 'e' in claves:

        usar_detectadas = input(
            f"¿Usar n={claves['n']} y e={claves['e']}? (y/n): "
        ).strip().lower()

        if usar_detectadas in ('y', 'yes', 'si', 's', ''):
            n = claves['n']
            e = claves['e']
            d = claves.get('d')
            p = claves.get('p')
            q = claves.get('q')

        else:
            n, e, d = obtener_claves_publicas()
            p = None
            q = None

    else:
        n, e, d = obtener_claves_publicas()
        p = None
        q = None

    modo = elegir_modo_rsa()

    if modo == "e":

        exponente = e

        # PARA DESCIFRAR HARÁ FALTA d
        clave_descifrado_nombre = "d"

        if d is None:
            clave_descifrado_valor = "(no disponible)"
        else:
            clave_descifrado_valor = d

    else:

        if d is None:
            d = int(input("d: "))

        exponente = d

        # PARA DESCIFRAR HARÁ FALTA e
        clave_descifrado_nombre = "e"
        clave_descifrado_valor = e

    seed_usada = pedir_seed()

    if seed_usada:

        abecedario_temp = generar_abecedario_con_seed(seed_usada)

        ABECEDARIO.update(abecedario_temp)

        NUMERO_A_LETRA.clear()

        NUMERO_A_LETRA.update(
            {v: k for k, v in ABECEDARIO.items()}
        )

    numeros = texto_a_numeros(mensaje)

    cifrados = []

    for v in numeros:

        if v == MARCADOR_DIGITO:
            cifrados.append(-pow(abs(v), exponente, n))

        elif v == 0:
            cifrados.append(0)

        else:
            cifrados.append(pow(v, exponente, n))

    pem_mensaje = numeros_a_pem_mensaje(cifrados)

    # PEM pública
    pem_publica = generar_clave_publica_pem(n, e)

    # PEM privada opcional
    pem_privada = None

    if (
        d is not None
        and p is not None
        and q is not None
    ):
        try:
            pem_privada = generar_clave_privada_pem(
                n, e, d, p, q
            )
        except:
            pass

    print()
    print("Mensaje cifrado (números):")
    print(" ".join(map(str, cifrados)))

    print()
    print(pem_mensaje)

    guardar = input(
        "\n¿Guardar resultado en fichero? (y/n): "
    ).strip().lower()

    if guardar in ('y', 'yes', 'si', 's', ''):

        nombre_salida = input(
            "Nombre del fichero de salida "
            "(ENTER = mensaje_cifrado.txt): "
        ).strip()

        if not nombre_salida:
            nombre_salida = "mensaje_cifrado.txt"

        contenido_salida = (
            "=== MENSAJE CIFRADO RSA ===\n"
            "\n"
            f"Seed            : "
            f"{seed_usada if seed_usada else '(normal)'}\n"
            f"Cifrado con     : "
            f"{'e (debes descifrar con d)' if modo == 'e' else 'd (debes descifrar con e)'}\n"
            "── PEM MENSAJE ──\n"
            f"{pem_mensaje}\n"
            "\n"
            "── PEM CLAVE PÚBLICA ──\n"
            f"{pem_publica}\n"
        )

        with open(nombre_salida, 'w', encoding='utf-8') as f:
            f.write(contenido_salida)

        print(f"✓ Guardado en: {nombre_salida}")


def descifrar_desde_txt():
    print()
    print("Descifrar desde fichero TXT")
    print("─" * 40)

    ruta = input("Ruta del fichero (o nombre si está en la misma carpeta): ").strip()

    if not os.path.exists(ruta):
        print(f"✗ No se encontró el fichero: {ruta}")
        return

    with open(ruta, 'r', encoding='utf-8') as f:
        contenido = f.read()

    # Detectar claves y mensaje cifrado
    claves = detectar_claves_en_txt(contenido)
    tipo_mensaje, datos_mensaje = detectar_mensaje_cifrado(contenido)

    print()
    if claves:
        print("Claves detectadas en el fichero:")
        for k, v in claves.items():
            print(f"  {k} = {v}")

    # Obtener números cifrados
    cifrados = None

    if tipo_mensaje == 'pem_mensaje':
        print()
        print("✓ Detectado mensaje cifrado en formato PEM")
        try:
            cifrados = pem_mensaje_a_numeros(datos_mensaje)
            print(f"  Números extraídos: {len(cifrados)}")
        except Exception as ex:
            print(f"✗ Error al parsear PEM: {ex}")

    elif tipo_mensaje == 'numeros':
        print()
        print("✓ Detectados números cifrados")
        cifrados = datos_mensaje
        print(f"  Cantidad: {len(cifrados)}")

    else:
        print()
        print("No se detectó mensaje cifrado en el fichero.")
        print()
        print("1 → Introducir números manualmente")
        print("2 → Pegar PEM de mensaje")
        print()
        opcion = input("Elige opción: ").strip()

        if opcion == "1":
            entrada = input("Números cifrados (separados por espacios): ")
            try:
                cifrados = list(map(int, entrada.split()))
            except ValueError:
                print("✗ Error al parsear números")
                return

        elif opcion == "2":
            pem = leer_bloque_pem()
            try:
                cifrados = pem_mensaje_a_numeros(pem)
            except Exception as ex:
                print(f"✗ Error al parsear PEM: {ex}")
                return

        else:
            print("Opción inválida")
            return

    if not cifrados:
        print("✗ No hay números para descifrar")
        return

    # Obtener n
    if 'n' in claves:
        usar_n = input(f"¿Usar n={claves['n']}? (y/n): ").strip().lower()
        if usar_n in ('y', 'yes', 'si', 's', ''):
            n = claves['n']
        else:
            n = int(input("n: "))
    else:
        n = int(input("n: "))

    # Determinar modo de descifrado automáticamente si es posible
    modo_detectado = claves.get('modo_cifrado')  # 'e' o 'd'

    if modo_detectado == 'e':
        # Cifrado con e → descifrar con d
        print()
        print("✓ Detectado automáticamente: cifrado con e → descifrar con d")
        if 'd' in claves:
            print(f"✓ Usando d={claves['d']} del fichero")
            exponente = claves['d']
        else:
            exponente = int(input("d: "))

    elif modo_detectado == 'd':
        # Cifrado con d → descifrar con e
        print()
        print("✓ Detectado automáticamente: cifrado con d → descifrar con e")
        if 'e' in claves:
            print(f"✓ Usando e={claves['e']} del fichero")
            exponente = claves['e']
        else:
            exponente = int(input("e: "))

    else:
        # No se pudo detectar el modo → preguntar manualmente
        print()
        print("No se detectó el modo de cifrado. El mensaje fue cifrado con:")
        print("1 → e (descifrar con d)")
        print("2 → d (descifrar con e)")
        print()
        modo = input("Elige opción: ").strip()

        if modo == "1" or modo == "":
            if 'd' in claves:
                usar_d = input(f"¿Usar d={claves['d']}? (y/n): ").strip().lower()
                exponente = claves['d'] if usar_d in ('y', 'yes', 'si', 's', '') else int(input("d: "))
            else:
                exponente = int(input("d: "))
        else:
            if 'e' in claves:
                usar_e = input(f"¿Usar e={claves['e']}? (y/n): ").strip().lower()
                exponente = claves['e'] if usar_e in ('y', 'yes', 'si', 's', '') else int(input("e: "))
            else:
                exponente = int(input("e: "))

    # Preguntar por seed
    if 'seed' in claves and claves['seed'] != '(normal)':
        usar_seed = input(f"¿Usar seed '{claves['seed']}'? (y/n): ").strip().lower()
        if usar_seed in ('y', 'yes', 'si', 's', ''):
            seed_usada = claves['seed']
        else:
            seed_usada = pedir_seed()
    else:
        seed_usada = pedir_seed()

    if seed_usada:
        abecedario_temp = generar_abecedario_con_seed(seed_usada)
        ABECEDARIO.update(abecedario_temp)
        NUMERO_A_LETRA.clear()
        NUMERO_A_LETRA.update({v: k for k, v in ABECEDARIO.items()})

    # Descifrar
    descifrados = []

    for c in cifrados:
        if c < 0:
            descifrados.append(MARCADOR_DIGITO)
        elif c == 0:
            descifrados.append(0)
        else:
            descifrados.append(pow(c, exponente, n))

    texto = numeros_a_texto(descifrados)

    print()
    print("Mensaje descifrado:")
    print(texto)


def menu_ficheros_txt():
    print()
    print("Cifrar/Descifrar desde TXT")
    print("─" * 40)
    print("1 → Cifrar mensaje (leer claves de TXT)")
    print("2 → Descifrar mensaje (desde TXT)")
    print()

    opcion = input("Elige opción: ").strip()

    if opcion == "1":
        cifrar_desde_txt()
    elif opcion == "2":
        descifrar_desde_txt()
    else:
        print("Opción inválida")


# ──────────────────────────────────────────────
# GUARDAR CLAVES EN FICHEROS TXT
# ──────────────────────────────────────────────

def guardar_claves_en_ficheros(n, e, d, p, q, phi, pem_pub, pem_priv,
                               mensaje_original=None, cifrados=None, pem_mensaje=None,
                               seed_usada=None, modo_cifrado=None):
    # Bloque de mensaje para añadir a los ficheros (si existe)
    if mensaje_original is not None:
        modo_texto = "e (clave pública)" if modo_cifrado == "e" else "d (clave privada)"
        seed_texto = seed_usada if seed_usada else "(normal)"

        bloque_mensaje = (
            "\n"
            "── Mensaje cifrado ──\n"
            f"Mensaje original: {mensaje_original}\n"
            f"Seed            : {seed_texto}\n"
            f"Cifrado con     : {modo_texto}\n"
            f"Números         : {' '.join(map(str, cifrados))}\n"
            "\n"
            f"{pem_mensaje}\n"
        )
    else:
        bloque_mensaje = ""

    contenido_publico = (
        "=== CLAVE PÚBLICA RSA ===\n"
        "\n"
        "── Números ──\n"
        f"n = {n}\n"
        f"e = {e}\n"
        "\n"
        "── PEM ──\n"
        f"{pem_pub}\n"
        + bloque_mensaje
    )

    contenido_privado = (
        "=== CLAVES RSA COMPLETAS ===\n"
        "\n"
        "── Números ──\n"
        f"p = {p}\n"
        f"q = {q}\n"
        f"n = {n}\n"
        f"φ(n) = {phi}\n"
        f"e = {e}\n"
        f"d = {d}\n"
        "\n"
        "── PEM clave pública ──\n"
        f"{pem_pub}\n"
        "\n"
        "── PEM clave privada ──\n"
        f"{pem_priv}\n"
        + bloque_mensaje
    )

    with open("clave_publica.txt", "w", encoding="utf-8") as f:
        f.write(contenido_publico)

    with open("claves_completas.txt", "w", encoding="utf-8") as f:
        f.write(contenido_privado)

    print()
    print("✓ Ficheros guardados:")
    print("  · clave_publica.txt    → n, e, PEM pública" + (" y mensaje cifrado" if mensaje_original else ""))
    print("  · claves_completas.txt → todas las claves en números y PEM" + (" y mensaje cifrado" if mensaje_original else ""))


# ──────────────────────────────────────────────
# GENERAR CLAVES
# ──────────────────────────────────────────────

def generar_claves_rsa():
    print()
    print("Generador RSA")
    print("─" * 40)

    entrada_cifras = input("Cifras para n (ENTER = aleatorio): ").strip()

    if entrada_cifras == "":
        cifras_n = random.randint(10, 30)
        print(f"Cifras aleatorias: {cifras_n}")
    else:
        cifras_n = int(entrada_cifras)

    bits_n = cifras_a_bits(cifras_n)
    bits_primo = max(bits_n // 2, 8)

    print()
    print("Generando primos...")

    p = primo_aleatorio(bits_primo)
    q = primo_aleatorio(bits_primo)

    while q == p:
        q = primo_aleatorio(bits_primo)

    n = p * q
    phi = (p - 1) * (q - 1)

    entrada_e = input("Cifras para e (ENTER = usar 65537): ").strip()

    if entrada_e == "":
        e = 65537
        if math.gcd(e, phi) != 1:
            e = 3
            while math.gcd(e, phi) != 1:
                e += 2
    else:
        cifras_e = int(entrada_e)
        bits_e = cifras_a_bits(cifras_e)

        e = None
        intentos = 0

        while True:
            candidato = primo_aleatorio(bits_e)
            if math.gcd(candidato, phi) == 1:
                e = candidato
                break
            intentos += 1
            if intentos > 1000:
                print("✗ No se encontró e válido con esas cifras, usando 65537")
                e = 65537
                if math.gcd(e, phi) != 1:
                    e = 3
                    while math.gcd(e, phi) != 1:
                        e += 2
                break

    d = pow(e, -1, phi)

    pem_pub = generar_clave_publica_pem(n, e)
    pem_priv = generar_clave_privada_pem(n, e, d, p, q)

    print()
    print("=" * 50)
    print(f"p = {p}")
    print(f"q = {q}")
    print(f"n = {n}")
    print(f"φ(n) = {phi}")
    print(f"e = {e}")
    print(f"d = {d}")
    print()
    print(pem_pub)
    print()
    print(pem_priv)

    # ── Cifrado opcional ──
    mensaje_original = None
    cifrados_msg     = None
    pem_mensaje      = None
    seed_usada       = None
    modo_cifrado     = None

    print()
    cifrar_ahora = input("¿Cifrar un mensaje con estas claves? (y/n): ").strip().lower()

    if cifrar_ahora in ("y", "yes", "si", "s"):
        print()
        print("1 → Cifrar con e (clave pública)")
        print("2 → Cifrar con d (clave privada)")
        print()
        modo_msg = input("Elige modo: ").strip()
        exponente_msg = d if modo_msg == "2" else e
        modo_cifrado = "d" if modo_msg == "2" else "e"

        # Preguntar por seed
        seed_usada = pedir_seed()

        if seed_usada:
            abecedario_temp = generar_abecedario_con_seed(seed_usada)
            ABECEDARIO.update(abecedario_temp)
            NUMERO_A_LETRA.clear()
            NUMERO_A_LETRA.update({v: k for k, v in ABECEDARIO.items()})
            print()
            print("Abecedario con seed aplicada:")
            mostrar_abecedario()

        texto_msg = input("Texto a cifrar: ")
        numeros_msg = texto_a_numeros(texto_msg)

        cifrados_msg = []
        for v in numeros_msg:
            if v == MARCADOR_DIGITO:
                cifrados_msg.append(-pow(abs(v), exponente_msg, n))
            elif v == 0:
                cifrados_msg.append(0)
            else:
                cifrados_msg.append(pow(v, exponente_msg, n))

        pem_mensaje      = numeros_a_pem_mensaje(cifrados_msg)
        mensaje_original = texto_msg

        print()
        print("Mensaje cifrado (números):")
        print(" ".join(map(str, cifrados_msg)))
        print()
        print(pem_mensaje)

    guardar_claves_en_ficheros(n, e, d, p, q, phi, pem_pub, pem_priv,
                                mensaje_original, cifrados_msg, pem_mensaje,
                                seed_usada, modo_cifrado)


# ──────────────────────────────────────────────
# MENÚS
# ──────────────────────────────────────────────

def menu_seeds():
    print()
    print("Seeds")
    print("─" * 40)
    print("1 → Seed personalizada")
    print("2 → Buscar seeds")
    print()

    opcion = input("Elige opción: ").strip()

    if opcion == "1":
        crear_seed_personalizada()

    elif opcion == "2":
        buscar_seed_string()

    else:
        print("Opción inválida")

# ─────────────────────────────
# RSA SIGN (INTEGRADO)
# ─────────────────────────────

def firmar_mensaje():
    print()
    print("Firma digital RSA")
    print("─" * 40)

    mensaje = input("Mensaje a firmar: ")

    hash_hex = hashlib.sha256(mensaje.encode()).hexdigest()
    hash_int = int(hash_hex, 16)

    print(f"Hash: {hash_int}")

    n, e, d = obtener_claves_publicas()

    if d is None:
        d = int(input("d: "))

    firma = pow(hash_int, d, n)

    print()
    print(f"Firma: {firma}")

    return firma, n, e


def verificar_firma():
    print()
    print("Verificar firma RSA")
    print("─" * 40)

    mensaje = input("Mensaje: ")
    firma = int(input("Firma: "))
    n = int(input("n: "))
    e = int(input("e: "))

    hash_hex = hashlib.sha256(mensaje.encode()).hexdigest()
    hash_int = int(hash_hex, 16) % n

    resultado = pow(firma, e, n)

    print()
    print("Hash esperado:", hash_int)
    print("Hash recibido:", resultado)

    if resultado == hash_int:
        print("✓ FIRMA VÁLIDA")
    else:
        print("✗ FIRMA INVÁLIDA")

# ═══════════════════════════════════════════════════════
#           PEM UNIVERSAL (INTEGRADO)
# ═══════════════════════════════════════════════════════


# ══════════════════════════════════════════════════════════════════
#  UTILIDADES COMUNES
# ══════════════════════════════════════════════════════════════════

def int_to_bytes(n):
    if n == 0:
        return b'\x00'
    length = (n.bit_length() + 7) // 8
    return n.to_bytes(length, byteorder='big')


def pem_a_bytes(pem_text):
    """Extrae los bytes crudos del interior de cualquier bloque PEM."""
    lines = pem_text.strip().splitlines()
    b64_lines = [l for l in lines if not l.startswith('-----')]
    return base64.b64decode(''.join(b64_lines))


def encode_pem_block(label, data_bytes):
    b64 = base64.encodebytes(data_bytes).decode('ascii')
    return f"-----BEGIN {label}-----\n{b64}-----END {label}-----"


def detectar_etiqueta(pem_text):
    """Extrae la etiqueta de la primera línea del PEM."""
    for line in pem_text.strip().splitlines():
        line = line.strip()
        if line.startswith("-----BEGIN "):
            return line.removeprefix("-----BEGIN ").removesuffix("-----").strip()
    return None


def leer_bloque_pem():
    """Lee un bloque PEM multilínea desde stdin."""
    print("Pega el bloque PEM y pulsa ENTER en una línea vacía al terminar")
    print("(o simplemente pega todo de una vez si tu terminal lo permite):")
    lineas = []
    while True:
        try:
            linea = input()
        except EOFError:
            break
        lineas.append(linea)
        if linea.strip().startswith("-----END"):
            break
    return "\n".join(lineas)


# ══════════════════════════════════════════════════════════════════
#  DER — usado por RSA PUBLIC KEY y RSA PRIVATE KEY
# ══════════════════════════════════════════════════════════════════

def decode_der_tlv(data, offset=0):
    tag = data[offset]; offset += 1
    lb  = data[offset]; offset += 1
    if   lb < 0x80:    length = lb
    elif lb == 0x81:   length = data[offset];                        offset += 1
    elif lb == 0x82:   length = (data[offset] << 8) | data[offset+1]; offset += 2
    else: raise ValueError("Longitud DER no soportada")
    value = data[offset:offset+length]
    return tag, value, offset+length

def decode_der_integer(value_bytes):
    return int.from_bytes(value_bytes, byteorder='big')

def encode_der_integer(n):
    raw = int_to_bytes(n)
    if raw[0] & 0x80:
        raw = b'\x00' + raw
    return encode_der_tlv(0x02, raw)

def encode_der_tlv(tag, value):
    length = len(value)
    if   length < 0x80:    lb = bytes([length])
    elif length < 0x100:   lb = bytes([0x81, length])
    elif length < 0x10000: lb = bytes([0x82, length >> 8, length & 0xFF])
    else: raise ValueError("Longitud demasiado grande")
    return bytes([tag]) + lb + value


# ══════════════════════════════════════════════════════════════════
#  MPI — usado por RSA SIGN, PUBLIC KEYS, RSA SIGN AND PUBLIC KEYS
#  Formato propio: [2B longitud][bytes del entero]
# ══════════════════════════════════════════════════════════════════

def encode_mpi(n):
    b = int_to_bytes(n)
    return struct.pack('>H', len(b)) + b

def decode_mpi(data, offset=0):
    length = struct.unpack_from('>H', data, offset)[0]
    offset += 2
    value  = int.from_bytes(data[offset:offset+length], byteorder='big')
    return value, offset+length


# ══════════════════════════════════════════════════════════════════
#  DECODIFICADORES
# ══════════════════════════════════════════════════════════════════

def decodificar_rsa_public_key(pem_text):
    """-----BEGIN RSA PUBLIC KEY----- → (n, e)  [formato DER propio del programa]"""
    der = pem_a_bytes(pem_text)
    tag, seq_val, _ = decode_der_tlv(der, 0)
    if tag != 0x30:
        raise ValueError("Se esperaba SEQUENCE (0x30)")
    off = 0
    _, n_bytes, off = decode_der_tlv(seq_val, off)
    _, e_bytes, off = decode_der_tlv(seq_val, off)
    return decode_der_integer(n_bytes), decode_der_integer(e_bytes)

def decodificar_rsa_private_key(pem_text):
    """-----BEGIN RSA PRIVATE KEY----- → (n, e, d, p, q)  [PKCS#1 DER]"""
    der = pem_a_bytes(pem_text)
    tag, seq_val, _ = decode_der_tlv(der, 0)
    if tag != 0x30:
        raise ValueError("Se esperaba SEQUENCE (0x30)")
    off = 0
    _, _,       off = decode_der_tlv(seq_val, off)  # version
    _, n_b,     off = decode_der_tlv(seq_val, off)
    _, e_b,     off = decode_der_tlv(seq_val, off)
    _, d_b,     off = decode_der_tlv(seq_val, off)
    _, p_b,     off = decode_der_tlv(seq_val, off)
    _, q_b,     off = decode_der_tlv(seq_val, off)
    return (decode_der_integer(n_b), decode_der_integer(e_b),
            decode_der_integer(d_b), decode_der_integer(p_b),
            decode_der_integer(q_b))

def decodificar_rsa_encrypted_message(pem_text):
    """-----BEGIN RSA ENCRYPTED MESSAGE----- → lista de enteros cifrados"""
    datos = pem_a_bytes(pem_text)
    numeros = []
    i = 0
    while i < len(datos):
        signo   = datos[i]; i += 1
        longitud = int.from_bytes(datos[i:i+4], byteorder='big'); i += 4
        num_bytes = datos[i:i+longitud]; i += longitud
        valor = int.from_bytes(num_bytes, byteorder='big')
        if signo == 1:
            valor = -valor
        numeros.append(valor)
    return numeros

def decodificar_rsa_sign(pem_text):
    """-----BEGIN RSA SIGN----- → entero de firma"""
    raw = pem_a_bytes(pem_text)
    return int.from_bytes(raw, byteorder='big')

def decodificar_public_keys(pem_text):
    """-----BEGIN PUBLIC KEYS----- → (n, e)  [formato MPI propio]"""
    datos = pem_a_bytes(pem_text)
    n, off = decode_mpi(datos, 0)
    e, _   = decode_mpi(datos, off)
    return n, e

def decodificar_rsa_sign_and_public_keys(pem_text):
    """-----BEGIN RSA SIGN AND PUBLIC KEYS----- → (firma, n, e)"""
    datos = pem_a_bytes(pem_text)
    firma, off = decode_mpi(datos, 0)
    n,     off = decode_mpi(datos, off)
    e,     _   = decode_mpi(datos, off)
    return firma, n, e


# ══════════════════════════════════════════════════════════════════
#  CODIFICADORES
# ══════════════════════════════════════════════════════════════════

def codificar_rsa_public_key(n, e):
    seq = encode_der_integer(n) + encode_der_integer(e)
    der = encode_der_tlv(0x30, seq)
    return encode_pem_block("RSA PUBLIC KEY", der)

def codificar_rsa_private_key(n, e, d, p, q):
    dp   = d % (p - 1)
    dq   = d % (q - 1)
    qInv = pow(q, -1, p)
    seq  = (encode_der_integer(0) + encode_der_integer(n) +
            encode_der_integer(e) + encode_der_integer(d) +
            encode_der_integer(p) + encode_der_integer(q) +
            encode_der_integer(dp) + encode_der_integer(dq) +
            encode_der_integer(qInv))
    der = encode_der_tlv(0x30, seq)
    return encode_pem_block("RSA PRIVATE KEY", der)

def codificar_rsa_encrypted_message(numeros):
    partes = []
    for num in numeros:
        es_neg  = num < 0
        abs_val = abs(num)
        nb      = int_to_bytes(abs_val) if abs_val else b'\x00'
        partes.append((b'\x01' if es_neg else b'\x00') +
                      len(nb).to_bytes(4, byteorder='big') + nb)
    return encode_pem_block("RSA ENCRYPTED MESSAGE", b''.join(partes))

def codificar_rsa_sign(firma):
    return encode_pem_block("RSA SIGN", int_to_bytes(firma))

def codificar_public_keys(n, e):
    return encode_pem_block("PUBLIC KEYS", encode_mpi(n) + encode_mpi(e))

def codificar_rsa_sign_and_public_keys(firma, n, e):
    return encode_pem_block("RSA SIGN AND PUBLIC KEYS",
                            encode_mpi(firma) + encode_mpi(n) + encode_mpi(e))


# ══════════════════════════════════════════════════════════════════
#  DECODIFICACIÓN AUTOMÁTICA
# ══════════════════════════════════════════════════════════════════

DECODIFICADORES = {
    "RSA PUBLIC KEY":            decodificar_rsa_public_key,
    "RSA PRIVATE KEY":           decodificar_rsa_private_key,
    "RSA ENCRYPTED MESSAGE":     decodificar_rsa_encrypted_message,
    "RSA SIGN":                  decodificar_rsa_sign,
    "PUBLIC KEYS":               decodificar_public_keys,
    "RSA SIGN AND PUBLIC KEYS":  decodificar_rsa_sign_and_public_keys,
}

def mostrar_resultado_decodificado(etiqueta, resultado):
    print()
    print(f"Tipo detectado: {etiqueta}")
    print("─" * 50)

    if etiqueta == "RSA PUBLIC KEY":
        n, e = resultado
        print(f"n = {n}")
        print(f"e = {e}")

    elif etiqueta == "RSA PRIVATE KEY":
        n, e, d, p, q = resultado
        print(f"n = {n}")
        print(f"e = {e}")
        print(f"d = {d}")
        print(f"p = {p}")
        print(f"q = {q}")

    elif etiqueta == "RSA ENCRYPTED MESSAGE":
        numeros = resultado
        print(f"Números cifrados ({len(numeros)} elementos):")
        print(" ".join(map(str, numeros)))

    elif etiqueta == "RSA SIGN":
        print(f"Firma (entero) = {resultado}")

    elif etiqueta == "PUBLIC KEYS":
        n, e = resultado
        print(f"n = {n}")
        print(f"e = {e}")

    elif etiqueta == "RSA SIGN AND PUBLIC KEYS":
        firma, n, e = resultado
        print(f"Firma = {firma}")
        print(f"n     = {n}")
        print(f"e     = {e}")

    else:
        print(resultado)


def decodificar_automatico(pem_text):
    etiqueta = detectar_etiqueta(pem_text)
    if etiqueta is None:
        print("✗ No se detectó una cabecera PEM válida.")
        return

    if etiqueta not in DECODIFICADORES:
        print(f"✗ Tipo '{etiqueta}' no reconocido.")
        print(f"  Tipos soportados: {', '.join(DECODIFICADORES.keys())}")
        return

    try:
        resultado = DECODIFICADORES[etiqueta](pem_text)
        mostrar_resultado_decodificado(etiqueta, resultado)
    except Exception as ex:
        print(f"✗ Error al decodificar: {ex}")


# ══════════════════════════════════════════════════════════════════
#  MENÚ CODIFICAR
# ══════════════════════════════════════════════════════════════════

def menu_codificar():
    print()
    print("Codificar → PEM")
    print("─" * 50)
    print("  [1] RSA PUBLIC KEY           (n, e)")
    print("  [2] RSA PRIVATE KEY          (n, e, d, p, q)")
    print("  [3] RSA ENCRYPTED MESSAGE    (lista de enteros cifrados)")
    print("  [4] RSA SIGN                 (entero de firma)")
    print("  [5] PUBLIC KEYS              (n, e  — formato firma)")
    print("  [6] RSA SIGN AND PUBLIC KEYS (firma, n, e)")
    print()

    op = input("Opción: ").strip()

    try:
        if op == "1":
            n = int(input("n: "))
            e = int(input("e: "))
            print("\n" + codificar_rsa_public_key(n, e))

        elif op == "2":
            n = int(input("n: "))
            e = int(input("e: "))
            d = int(input("d: "))
            p = int(input("p: "))
            q = int(input("q: "))
            print("\n" + codificar_rsa_private_key(n, e, d, p, q))

        elif op == "3":
            entrada = input("Números cifrados separados por espacios: ")
            nums = list(map(int, entrada.split()))
            print("\n" + codificar_rsa_encrypted_message(nums))

        elif op == "4":
            firma = int(input("Firma (entero): "))
            print("\n" + codificar_rsa_sign(firma))

        elif op == "5":
            n = int(input("n: "))
            e = int(input("e: "))
            print("\n" + codificar_public_keys(n, e))

        elif op == "6":
            firma = int(input("Firma (entero): "))
            n     = int(input("n: "))
            e     = int(input("e: "))
            print("\n" + codificar_rsa_sign_and_public_keys(firma, n, e))

        else:
            print("Opción inválida")

    except Exception as ex:
        print(f"✗ Error: {ex}")


# ══════════════════════════════════════════════════════════════════
#  MENÚ PRINCIPAL
# ══════════════════════════════════════════════════════════════════

TIPOS_SOPORTADOS = "\n".join(
    f"  · {k}" for k in DECODIFICADORES
)

def main():
    print()
    print("╔══════════════════════════════════════════╗")
    print("║     Herramienta PEM Universal            ║")
    print("╚══════════════════════════════════════════╝")
    print()
    print("Tipos de PEM soportados:")
    print(TIPOS_SOPORTADOS)
    print()
    print("─" * 50)
    print("  [1] Decodificar PEM  → números / claves")
    print("  [2] Codificar        → PEM")
    print()

    op = input("Opción: ").strip()

    if op == "1":
        pem = leer_bloque_pem()
        decodificar_automatico(pem)

    elif op == "2":
        menu_codificar()

    else:
        print("Opción inválida")


def menu_pem_universal():
    print()
    print("PEM UNIVERSAL")
    print("─" * 40)
    print("1 → Decodificar PEM")
    print("2 → Codificar PEM")
    print()

    opcion = input("Elige opción: ").strip()

    if opcion == "1":
        pem = leer_bloque_pem()
        decodificar_automatico(pem)

    elif opcion == "2":
        menu_codificar()

    else:
        print("Opción inválida")

def menu_modo_avanzado():
    print()
    print("Modo avanzado")
    print("─" * 40)
    print("1 → Generar claves")
    print("2 → Seeds")
    print("3 → Cifrar/Descifrar desde TXT")
    print("4 → Firma digital RSA")
    print("5 → PEM UNIVERSAL")
    print()

    opcion = input("Elige opción: ").strip()

    if opcion == "1":
        generar_claves_rsa()

    elif opcion == "2":
        menu_seeds()

    elif opcion == "3":
        menu_ficheros_txt()

    elif opcion == "4":
        print()
        print("1 → Firmar mensaje")
        print("2 → Verificar firma")
        print()

        op = input("Elige: ").strip()

        if op == "1":
            firmar_mensaje()
        elif op == "2":
            verificar_firma()

    elif opcion == "5":
        menu_pem_universal()

def start():
    print()
    print("Cifrado y descifrado RSA")
    print("─" * 40)
    print("1 → Números")
    print("2 → Letras")
    print("3 → Modo avanzado")
    print()

    opcion = input("Elige opción: ").strip()

    # NÚMEROS
    if opcion == "1":

        print()
        print("Números")
        print("─" * 40)
        print("1 → Cifrar")
        print("2 → Descifrar")
        print()

        accion = input("Elige opción: ").strip()

        if accion == "1":
            cifrar_numero()

        elif accion == "2":
            descifrar_numero()

        else:
            print("Opción inválida")

    # LETRAS
    elif opcion == "2":

        seed = pedir_seed("Introduce seed (vacío = normal, 'random' = aleatoria): ")

        if seed:
            ABECEDARIO.update(
                generar_abecedario_con_seed(seed)
            )

            NUMERO_A_LETRA.clear()

            NUMERO_A_LETRA.update(
                {v: k for k, v in ABECEDARIO.items()}
            )

        mostrar_abecedario()

        print()
        print("Letras")
        print("─" * 40)
        print("1 → Cifrar")
        print("2 → Descifrar")
        print()

        accion = input("Elige opción: ").strip()

        if accion == "1":
            cifrar_texto()

        elif accion == "2":
            descifrar_texto()

        else:
            print("Opción inválida")

    # MODO AVANZADO
    elif opcion == "3":
        menu_modo_avanzado()

    else:
        print("Opción inválida")

    print()

    reiniciar = input("¿Reiniciar? (y/n): ").strip().lower()

    if reiniciar in ("y", "yes", "si", "s", ""):
        start()


start()
