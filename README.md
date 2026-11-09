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

Mises à jour : l'app les détecte toute seule (bandeau bleu « Mise à jour disponible » sur
l'accueil, ou Journal > « Rechercher une mise à jour »). Ta collection est gardée.

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
- Chargés en arrière-plan à un rythme tranquille (≈ 1 requête / 4 s). Chargement rapide :
  les listes de chaque console (150 jeux par page) remplissent d'un coup la plupart des
  jeux, les autres sont cherchés un par un. Ensuite c'est gardé 30 jours.
- Si PriceCharting demande une vérification anti-robot, l'app bascule sur son navigateur
  intégré ; si une case « Je ne suis pas un robot » apparaît, l'app te l'affiche :
  touche-la et les prix reprennent. « Plus tard » met les prix en pause 30 min.
- Si un jeu est mal reconnu : fiche du jeu > « Corriger la fiche » et coller le lien
  PriceCharting du bon jeu. Tu peux aussi saisir ton propre prix.

## Ta collection est protégée
- Copie de sécurité automatique dans `Documents/sauvegardes_collection/` : à chaque
  lancement, toutes les heures et **avant chaque mise à jour** (30 dernières gardées,
  la plus complète n'est jamais supprimée).
- Si le fichier de la collection est abîmé ou disparaît, l'app recharge la dernière
  sauvegarde au lieu de repartir de zéro (le fichier abîmé est mis de côté).
- Journal > « Restaurer une sauvegarde » : choisir une sauvegarde (date + nombre de jeux)
  ou « Reconstituer depuis le journal » (rejoue les ajouts/retraits notés).

## Un problème ?
Accueil > « Journal / signaler un problème » > « Copier le rapport », puis colle-le à Claude.

## Fichiers (dans Documents/)
| Fichier | Contenu |
|---|---|
| `collection_jeux.json` | jeux possédés, conditions, prix saisis, fiches corrigées |
| `prix_cache.json` | prix déjà chargés |
| `jaquettes/` | jaquettes téléchargées |
| `sauvegardes_collection/` | copies de sécurité de ta collection |
| `valeur_collection.csv` | dernier rapport de valeur |
| `pricecharting_token.txt` | clé API PriceCharting (facultative) |
