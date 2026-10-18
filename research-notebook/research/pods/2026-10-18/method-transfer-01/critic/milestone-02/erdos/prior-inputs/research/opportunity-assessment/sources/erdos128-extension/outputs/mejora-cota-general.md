# Derivación de una cota general de 0,026166 n²

El argumento de este documento da una mejora general de la cota estudiada, usando los ingredientes externos identificados abajo. Se han comprobado las constantes con aritmética racional y se ha ejecutado el verificador del certificado de ciclos. No se ha formalizado esta extensión en Lean ni se afirma que sea inédita. **No resuelve Erdős #128: 0,026166 todavía es mayor que 0,02.**

## Enunciado

Todo grafo simple sin triángulos con n≥1 vértices tiene un conjunto de floor(n/2) vértices que induce menos de

\[
\frac{13083}{500000}n^2=0.026166\,n^2
\]

aristas. Para n=0, el conjunto vacío satisface la versión no estricta y también la conjetura original.

Trabajamos con mitades fraccionarias f:V→[0,1] de suma n/2 y coste normalizado n⁻²Σᵤᵥ∈ᴱ fᵤfᵥ. Denotamos el coste mínimo por β*. Una transferencia entre dos coordenadas parciales hace que el coste sea afín o cóncavo. Por ello existe un minimizador con a lo sumo una coordenada parcial. Para n par es una mitad entera; para n impar, eliminar la única coordenada igual a 1/2 da floor(n/2) vértices sin aumentar el coste.

## Ingredientes externos

Usamos D₂(G)≤2n²/47, donde D₂ es el mínimo número de aristas internas de una bipartición. El resultado para órdenes suficientemente grandes es de [Balogh, Clemen y Lidický, teorema 1.2(a)](https://arxiv.org/html/2103.14179v1). Se extiende a todos los órdenes mediante ampliaciones equilibradas: D₂(G(t))=t²D₂(G). Para ver esta identidad, representar la fracción de cada clase de gemelos puesta a un lado da una función afín en cada coordenada; su mínimo se alcanza colocando cada clase entera a un lado.

También usamos el lema cúbico y el certificado

\[
t(C_4,G)\ge\rho^3-\gamma\rho,
\quad \gamma=\frac3{64}+\frac1{50000000000},
\quad \rho=2e(G)/n^2,
\]

del [trabajo de Sarid](https://github.com/aimir/erdos-128-sparse-halves). El lema cúbico asegura que, en un grafo ponderado de masa de aristas μ, algún vértice satisface d(e−μd)≥4μ³. La salida de la verificación local del certificado está en `c4-certificate-verification.txt`: pasaron los 38 grafos de seis vértices y los 34 cuadrados racionales.

Finalmente, usamos la desigualdad de anclaje β*≤ρ/8−t(C₄,G)/(4ρ), para grado máximo menor que n/2. Es el argumento de vecindades de [Razborov, proposición 1.1](https://arxiv.org/html/2104.09406v2), con t(C₄,G)=hom(C₄,G)/n⁴. Si el grado máximo es al menos n/2, hay una mitad independiente y no hace falta esa desigualdad.

## 1. Refuerzo de la perturbación

Nota de normalización del ingrediente anterior: el símbolo C₄ de Razborov es tres veces hom(C₄,G)/n⁴. Por ello su denominador 12ρ se convierte en 4ρ con el t(C₄,G) utilizado aquí; no se ha sustituido una constante sin cambiar la normalización.

Sea H un grafo ponderado sin triángulos, con pesos positivos wᵥ que suman uno. Definamos

\[
\mu=\sum_{uv\in E(H)}w_uw_v,
\quad d_x=\sum_{y\in N(x)}w_y,
\quad e_x=\sum_{y\in N(x)}w_y d_y,
\quad S_x=d_x(e_x-\mu d_x).
\]

Para α∈[0,1], pongamos a=min(α,1−α) y

\[
\widetilde L(a,\mu)=\min\{4a^2,\ a(1-a)(1+8\mu^2)\}.
\]

**Lema.** Para cualquier funcional lineal ℓ, el perfil constante α puede reemplazarse por otro π∈[0,1] con la misma media ponderada y tal que

\[
\sum_{uv\in E(H)}w_uw_v\pi_u\pi_v+\ell(\pi)
\le \alpha^2\mu+\ell(\alpha)
-4\widetilde L(a,\mu)\mu^3.
\]

**Prueba.** Los casos μ=0 o a=0 son inmediatos. El lema cúbico proporciona un vértice x con Sₓ≥4μ³. Abreviemos d=dₓ. La vecindad de x es independiente, por lo que eₓ es exactamente la masa de aristas entre N(x) y su complemento. En particular eₓ≤μ. Así,

\[
4\mu^3\le S_x\le\mu d(1-d),
\qquad d(1-d)\ge4\mu^2.
\]

En consecuencia, tanto d como 1−d pertenecen a [4μ²,1−4μ²].

El vector φ=𝟙_{N(x)}−d tiene media ponderada cero. Sobre la recta α+tφ, el término cuadrático del coste es −Sₓt². Sean t₊ y t₋ las distancias hasta los dos extremos factibles:

\[
t_+=\min\left\{\frac{1-\alpha}{1-d},\frac\alpha d\right\},
\qquad
t_-=\min\left\{\frac\alpha{1-d},\frac{1-\alpha}{d}\right\}.
\]

Al promediar los dos extremos con pesos t₋/(t₊+t₋) y t₊/(t₊+t₋), los términos lineales se cancelan y el ahorro es t₊t₋Sₓ. Uno de los extremos ahorra al menos esa cantidad.

Por simetría podemos calcular el producto usando a≤1/2. Si a≤d≤1−a,

\[
t_+t_-=\frac{a^2}{d(1-d)}\ge4a^2.
\]

En los otros dos casos,

\[
t_+t_-=\frac{a(1-a)}{\max(d,1-d)^2}
\ge\frac{a(1-a)}{(1-4\mu^2)^2}
\ge a(1-a)(1+8\mu^2).
\]

La última desigualdad se sigue de (1−q)⁻²≥1+2q, con q=4μ²≤1/4: al multiplicar, la diferencia es q²(3−2q)≥0. Por tanto t₊t₋≥L̃(a,μ), y combinarlo con Sₓ≥4μ³ prueba el lema. □

El cambio respecto de la perturbación anterior consiste en conservar la relación Sₓ≤μd(1−d). El vértice elegido por el lema cúbico no puede tener grado ponderado arbitrariamente próximo a cero o a uno.

## 2. Caso de densidad alta

Fijemos

\[
R=\frac{31867}{100000}.
\]

Para ρ≥R, la desigualdad de anclaje y el certificado dan

\[
\beta^*\le \frac\rho8-\frac{\rho^2}{4}+\frac\gamma4.
\]

Esta expresión decrece para ρ>1/4. En ρ=R vale exactamente

\[
\frac{1308242889}{50000000000}
=0.02616485778<0.026166.
\]

## 3. Caso de densidad baja

Supongamos ρ≤R. Tomemos una bipartición X,Y con |X|≤|Y| y

\[
I_X+I_Y\le I=\frac2{47},
\qquad I_X=e(X)/n^2,\quad I_Y=e(Y)/n^2.
\]

Escribamos

\[
c=\frac{n}{2|Y|},\qquad a=1-c\in[0,1/2],
\qquad \mu=4c^2 I_Y.
\]

Entonces 0≤μ≤4Ic². Las funciones 1_X+a1_Y y c1_Y son mitades fraccionarias. Si J=I_X+I_Y, sus costes son

\[
B_1=\frac{a\rho}{2}+cJ-\frac{1+a}{4c}\mu,
\qquad B_2=\frac\mu4.
\]

Aplicamos el lema dentro de Y. Las contribuciones de aristas hacia X son lineales, y la normalización multiplica el ahorro por |Y|²/n²=1/(4c²). Por tanto,

\[
\beta^*\le\min(B_1,B_2)-\frac{\mu^3}{c^2}\widetilde L(a,\mu).
\]

Sustituir ρ por R y J por I solo puede aumentar el primer término. Definamos

\[
P(a)=aR/2+cI,
\quad M(a,\mu)=\min\left\{P(a)-\frac{1+a}{4c}\mu,\frac\mu4\right\},
\]

\[
T_1=4a^2\mu^3/c^2,
\qquad T_2=(a/c)(\mu^3+8\mu^5).
\]

La expresión a maximizar es F=max(M−T₁,M−T₂).

### Maximización en μ

Los dos términos de M coinciden en ν(a)=2cP(a). Para μ≤ν, M=μ/4. En todo el dominio,

\[
\partial_\mu T_1\le12I^2=48/2209<1/4,
\]

porque μ≤4Ic² y a²c²≤1/16. Además,

\[
\partial_\mu T_2\le3(4I)^2+40(4I)^4
=587968/4879681<1/4.
\]

Luego ambas funciones M−Tᵢ crecen hasta ν. Después, M decrece y cada Tᵢ crece. Ambas alcanzan su máximo admisible en

\[
\mu=\min\{2cP,4Ic^2\}.
\]

Las dos alternativas coinciden en

\[
a_*=\frac I{R/2+I}=\frac{400000}{1897749},
\qquad c_*=\frac{1497749}{1897749}.
\]

### Maximización en a, antes de a*

Para 0≤a≤a*, se tiene μ=2cP y M=h=cP/2. Los ahorros quedan

\[
S_1=32a^2cP^3,
\qquad S_2=8ac^2P^3+256ac^4P^5.
\]

Sea δ=R/2−I. En este intervalo,

\[
a<11/50,\quad P<71/1000,\quad 0<\delta<3/25,
\]

y

\[
h'\ge h'(a_*)=\frac{9488367383}{759099600000}>1/100.
\]

Derivando los dos ahorros y acotando superiormente sus términos positivos se obtiene

\[
S_1'\le32aP^2(2P+3a\delta)
<\frac{30664403}{3906250000}<1/100,
\]

\[
S_2'\le8P^2(P+3a\delta)+256P^4(P+5a\delta)
<\frac{28819764993}{3906250000000}<1/100.
\]

Por ello h−S₁ y h−S₂ son crecientes.

### Maximización en a, después de a*

Para a*≤a≤1/2, μ=4Ic² y M=Ic². Las dos funciones son

\[
F_1=Ic^2-256I^3a^2c^4,
\]

\[
F_2=Ic^2-64I^3ac^5-8192I^5ac^9.
\]

Sus derivadas satisfacen

\[
F_1'\le-2Ic(1-64I^2)<0,
\]

\[
F_2'\le-2Ic(1-64I^2-16384I^4)<0,
\]

pues 64I²=256/2209<1 y 64I²+16384I⁴=827648/4879681<1. Estas cotas usan solamente a≤1/2 y c≤1 al acotar las posibles correcciones positivas de las derivadas.

Ambas funciones crecen antes de a* y decrecen después. Su máximo, y por tanto el de F, está en a*.

### Valor máximo

En ese punto,

\[
\mu_*=\frac{381830139064}{3601451267001},
\qquad
4a_*^2\le a_*c_*(1+8\mu_*^2).
\]

Por tanto el ahorro menor es T₁, y la cota del caso de densidad baja es

\[
Ic_*^2-256I^3a_*^2c_*^4
=\frac{1222245031293820230700164127328578766}
{46712448010755312062426789683220801001}
\approx0.026165296047263555
<0.026166.
\]

Los dos casos cubren todas las densidades. El redondeo inicial da el enunciado sobre floor(n/2) vértices. □

## Evidencia y alcance

`verify-improved-bound.py` comprueba con fracciones exactas todas las comparaciones racionales usadas arriba. También contrastó el lema reforzado en 1.480 casos ponderados sobre los 38 grafos sin triángulos de seis vértices. Estas pruebas finitas corroboran el lema; su justificación para todos los grafos es la demostración algebraica de la sección 1.

El certificado de ciclos se verificó con el programa del autor, descargado del repositorio citado. Su SHA-256 local fue `0151443fd1960ea1e861ae20f38dc8f834757c80098d7182d9574f538ce59bf2`. Esta ejecución verifica ese ingrediente, no formaliza automáticamente la extensión presente.

La mejora es general, pero aún queda una diferencia de 0,006166 en el coeficiente respecto del objetivo de Erdős. Incluso una bipartición equilibrada con coste interno 2n²/47 solo da, tomando el mejor lado, n²/47>n²/50; en ese extremo a=0 y la perturbación usada aquí no mejora nada. Por ello este argumento todavía requiere otra idea para llegar a la constante solicitada.
