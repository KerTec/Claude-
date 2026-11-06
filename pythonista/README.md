# Ma collection de jeux (Pythonista)

Checklist de collection multi-consoles pour **Pythonista 3** (iPhone / iPad) :
PS2, N64, DS, 3DS, Xbox 360, Wii, GameCube, Switch.

## Installation
1. Copier `collection_jeux.py` dans Pythonista.
2. Lancer le script (▶).

## Utilisation
- **Mode cocher** : toucher un jeu le coche / décoche (sauvegarde automatique).
- **Mode infos & prix** : toucher un jeu ouvre son menu : cocher, copier le nom,
  voir le prix, saisir son prix, choisir la condition (disque seul / complet / neuf),
  ouvrir PriceCharting, eBay (ventes réalisées) ou Leboncoin.
- **Recherche** : par jeu ou par série, sans souci d'accents (« okami » → « Ōkami »).
- **Exporter** : copie la checklist de la console dans le presse-papiers.
- **Valeur console / totale** : rapport min / milieu / max + CSV
  `Documents/valeur_collection.csv` (séparateur `;`, s'ouvre dans Numbers / Excel).

## Prix
- Sans clé API : une requête PriceCharting seulement quand tu touches « Voir le prix »
  (8 s minimum entre deux requêtes, pause d'1 h si le site bloque). Prix gardés 30 jours.
- Avec une clé API PriceCharting (abonnement) : chargement automatique.
  Menu d'un jeu > « Clé API PriceCharting », ou fichier `Documents/pricecharting_token.txt`.

## Fichiers (dans Documents/)
| Fichier | Contenu |
|---|---|
| `collection_jeux.json` | jeux possédés, conditions, prix saisis (migration auto depuis `collection_ps2.json`) |
| `prix_cache.json` | prix déjà consultés |
| `pricecharting_token.txt` | clé API (facultative) |
| `valeur_collection.csv` | dernier rapport de valeur |
| `debug_pricecharting.html` | dernière page non reconnue (diagnostic) |
