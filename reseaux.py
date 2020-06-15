from collections import deque
from functools import partial
from sys import setrecursionlimit
setrecursionlimit(10**6)


# Générateur de nombres (pseudo) aléatoires.
u0 = 5

u = [u0]
v = [u0]
for _ in range(10**6):
    u.append(u[-1] * 15091 % 64007)
    v.append(v[-1] * 1129 % 63997)


def w(i, n):
    return u[i] % n, v[i] % n


# Graphe aléatoire.
def G(n, t):
    g = [set() for _ in range(n)]
    for i in range(t):
        u, v = w(i, n)
        if u != v:
            g[u].add(v)
            g[v].add(u)
    return g


def deg_moy(n, t):
    g = G(n, t)
    return sum(map(len, g)) / len(g)


def BFS(g, s):
    file = deque([s])
    distance = [float('inf')] * len(g)
    distance[s] = 0
    while file:
        u = file.popleft()
        for v in g[u]:
            if distance[v] == float('inf'):
                distance[v] = distance[u] + 1
                file.append(v)
    return distance


def di(n, t, i=0):
    ''' Distance maximale finie entre i et un sommet de G(n, t). '''
    g = G(n, t)
    return max(filter(lambda x: x != float('inf'), BFS(g, i)))


def diam(n, t):
    ''' Diamètre de G(n, t) '''
    return max(map(partial(di, n, t), range(n)))


def dfs(g, marque, u):
    for v in g[u]:
        if not marque[v]:
            marque[v] = True
            dfs(g, marque, v)


def nb_comp_connexes(n, t):
    g = G(n, t)
    marque = [False] * n
    nb = 0
    for u in range(n):
        if not marque[u]:
            nb += 1
            marque[u] = True
            dfs(g, marque, u)
    return nb


'''
On utilise une structure de donnée union find.
espace : O(n)
temps: pour n unions
    - Avec UnionFind en O(alpha(n)) : O(alpha(n) * n) presque linéaire.
    - Avec UnionFind en O(log(n)) (arbre équilibré) : O(log(n) * n)
    - Avec UnionFind sans équilibrage : O(n^2)

Analyse :
On s'interresse à la hauteur des arbres car la complexité est en theta(hauter).
On traite uniquement le cas avec l'union par rang et sans la compression de chemin.
On montre pour chaque classes l'invariant suivant :
    hauteur = rang et 2^(rang) <= nombre de noeuds
On a donc hauteur = O(log(nombre de noeuds)) <= O(log(n)).
theta(log(nombre de noeuds))

Quand on ajoute la compression de chemin :
    hauteur <= rang et donc le mếme raisonnement s'applique. Toute fois cela ne donne qu'une majoration. En effet la complexité est en O(alpha(n)) (réciproque de Ackerman) soit en temps constant pour tout nombre stockable dans notre univers. On peut même montrer que le problème est omega(alpha(n)) en complexité amortie. Notre implémentation de UnionFind est donc optimale.
'''


class UnionFind:
    def __init__(self, n):
        self.n = n
        self.parent = list(range(n))
        self.rang = [0] * n
        self.nb_classes = n

    def __str__(self):
        return str(self.parent)

    def __repr__(self):
        print(str(self))

    def __len__(self):
        return self.nb_classes

    def find_repr(self, x):
        if x == self.parent[x]:
            return x
        representant = self.find_repr(self.parent[x])
        self.parent[x] = representant  # Compression de chemin.
        return representant

    def union(self, x, y):
        repr_x = self.find_repr(x)
        repr_y = self.find_repr(y)
        r_x = self.rang[repr_x]
        r_y = self.rang[repr_y]
        # Union par rang.
        if r_y < r_x:
            self.parent[repr_y] = repr_x
        else:
            self.parent[repr_x] = repr_y
        if r_x == r_y:
            self.rang[repr_x] = r_x + 1
        if repr_x != repr_y:
            self.nb_classes -= 1


'''
espace : O(n + t)
temps : O(t * (log(t) + alpha(n))) ou O(t * log(t * n)) en fonction de la version de union find.


Remarque : On obtient bien un arbre par acyclicité et connexité. Il est couvrant car contient tou les noeuds

Preuve de correction :
On travaille avec un graphe G ayant plus de 2 sommets.

Notations :
    - arbre couvrant de poids maximal dans le graphe G = ACM(G)
    - |G| = nombre de sommets de G

Montrons qu'un ACM(G) contient une arete de poids maximal dans G :
    Soit T arbre couvrant ne contenant pas d'arete de poids maximal.
    Notons (u, v) une arete de poids maximal dans G.
    (u, v) n'est pas dans T.
    T est couvrant et |G| >= 2 donc il existe un somment s tel que (u, s) soit dans T.
    On considère T' le graphe où l'on a enlevé (u, s) et rajouté (u, v) par rapport à T.

    Au tableau on peut facilement montrer que :
        T' est connexe.
        T' est acyclique.
        T' est un arbre couvrant.
        T' est de poids > à celui de T.
    D'où T n'est pas un ACM(G)
    Par contraposition, cela prouve le résultat.

Soit T arbre dans un graphe G tel que il existe (u, v) dans T une arete de poids maximal de G.
On considère maintenant le morphisme phi qui contracte l'arete (u, v).
phi(T) est ACM(phi(G)) si et seulement si T est ACM(G).

Finalement en combinant les deux résultats:
(u, v) dans T et (u, v) de poids maximal dans G et phi(T) ACM(phi(G)) implique T est ACM(G).

Ainsi on peut montrer par récurrence sur |G| que l'algorithme glouton renvoie effectivement un ACM(G). (On traite facilement les cas de base).
'''


def poids_arbre_couvrant_max(n, t):
    ''' Kruskal. '''
    poids_liste = []
    foret = UnionFind(n)
    poids = lambda w: (u[sum(w)] / 64007, min(w), max(w))  # Aléatoire.
    aretes = sorted(list(map(poids, [w(i, n) for i in range(t)])), reverse=True)
    for p, x, y in aretes:
        if foret.find_repr(x) != foret.find_repr(y):
            foret.union(x, y)
            poids_liste.append(p)
        if len(foret) == 1:
            break
    return poids_liste

