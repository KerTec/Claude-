# Ma collection de jeux (Pythonista)

Un « Pokédex » de jeux vidéo pour **Pythonista 3** (iPhone / iPad) :
PS2, N64, DS, 3DS, Xbox 360, Wii, GameCube, Switch — 449 jeux.

## Installation sur iPhone
1. Installer **Pythonista 3** (App Store).
2. Ouvrir la console de Pythonista (icône `>_`), coller cette ligne et valider :
   ```python
   import requests, os; open(os.path.expanduser('~/Documents/collection_jeux.py'), 'w', encoding='utf-8').write(requests.get('https://raw.githubusercontent.com/KerTec/Claude-/main/collection_jeux.py').text)
   ```
3. Ouvrir `collection_jeux.py` dans la liste des fichiers et toucher **▶**.

Pour mettre à jour le script plus tard : refaire l'étape 2 (ta collection est gardée).

## Ce que fait l'app
- **Accueil** : une carte par console avec progression, nombre de jeux obtenus et valeur.
- **Grille de jaquettes** : jeux obtenus en couleur avec ✓, manquants en gris,
  numéro (#001…), prix et rareté (★ Commun → ★★★★★ Légendaire) sur chaque case.
  Recherche, filtres, tri (n°, prix, rareté, A–Z) et mode « Toucher : cocher ».
- **Fiche d'un jeu** : grande jaquette, prix par condition (disque seul / complet / neuf),
  ventes récentes, « Je l'ai », mon prix, liens eBay / Leboncoin / PriceCharting.
- **Rapport de valeur** de toute la collection + CSV (`Documents/valeur_collection.csv`).
- **Exporter** : checklist de toutes les consoles copiée dans le presse-papiers.

## Prix et jaquettes
- Automatiques, **sans clé API** : source PriceCharting (versions PAL, ou US si le jeu
  n'est jamais sorti en Europe), convertis en euros au taux du jour.
- Chargés en arrière-plan à un rythme tranquille (≈ 1 requête / 4 s). Au premier
  lancement, compter ≈ 30 min pour tout le catalogue ; ensuite c'est gardé 30 jours.
- Si un jeu est mal reconnu : fiche du jeu > « Corriger la fiche » et coller le lien
  PriceCharting du bon jeu. Tu peux aussi saisir ton propre prix.

## Fichiers (dans Documents/)
| Fichier | Contenu |
|---|---|
| `collection_jeux.json` | jeux possédés, conditions, prix saisis, fiches corrigées |
| `prix_cache.json` | prix déjà chargés |
| `jaquettes/` | jaquettes téléchargées |
| `valeur_collection.csv` | dernier rapport de valeur |
| `pricecharting_token.txt` | clé API PriceCharting (facultative) |
