# Ma collection de jeux (Pythonista)

Un « Pokédex » de jeux vidéo pour **Pythonista 3** (iPhone / iPad) :
26 consoles (rétro, Nintendo, PlayStation, Xbox, Sega) — 820 jeux en sélection, plus le
catalogue complet de chaque console.

## Installation sur iPhone
1. Installer **Pythonista 3** (App Store).
2. Ouvrir la console de Pythonista (icône `>_`), coller cette ligne et valider :
   ```python
   import requests, os; open(os.path.expanduser('~/Documents/collection_jeux.py'), 'w', encoding='utf-8').write(requests.get('https://raw.githubusercontent.com/KerTec/Claude-/main/collection_jeux.py').text)
   ```
3. Ouvrir `collection_jeux.py` dans la liste des fichiers et toucher **▶**.
   C'est un petit lanceur : au 1er lancement il télécharge le code de l'app dans
   `Documents/.collection_jeux/` (jamais ouvert dans l'éditeur, plus léger et plus rapide).

Mises à jour : l'app les détecte toute seule (bandeau bleu « Mise à jour disponible » sur
l'accueil, ou Journal > « Rechercher une mise à jour »). Ta collection est gardée.

## Ce que fait l'app
- **Accueil** : une carte par console avec progression, nombre de jeux obtenus et valeur.
- **Grille de jaquettes** : jeux obtenus en couleur avec ✓, manquants en gris,
  numéro (#001…), prix et rareté (★ Commun → ★★★★★ Légendaire) sur chaque case.
  Recherche, filtres, tri (n°, prix, rareté, A–Z) et mode « Toucher : cocher ».
- **Fiche d'un jeu** : grande jaquette, prix par condition (disque seul / complet / neuf),
  ventes récentes, « Je l'ai », mon prix, liens eBay / Leboncoin / PriceCharting.
- **Prix figé à l'ajout** : ▲ vert / ▼ rouge selon l'évolution, prix payé et bénéfice,
  nombre d'exemplaires, note libre, courbe du prix de chaque jeu.
- **Mes jeux** : tous mes jeux, toutes consoles, 4 tris, export CSV complet.
- **Recherche** sur toutes les consoles et **scanner de code-barres**.
- **Liste de souhaits** avec alerte de baisse de prix, et **idées d'achat** par budget.
- **Statistiques** : valeur, courbe d'évolution, top 10, rareté, valeur par console,
  image à partager, 20 **succès** à débloquer.
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
- Copie aussi dans **iCloud Drive** (dossier Pythonista > « Sauvegarde collection jeux ») :
  elle survit à la suppression de l'app et au changement d'iPhone.
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
| `ma_collection.csv` | export complet (Mes jeux > Exporter) |
| `valeur_historique.json`, `prix_historique.json` | valeur et prix jour par jour (courbes) |
| `catalogue_complet/` | tous les jeux de chaque console |
| `pricecharting_token.txt` | clé API PriceCharting (facultative) |

## Crédits
Images des consoles : [RetroArch / libretro – retroarch-assets](https://github.com/libretro/retroarch-assets) (thème XMB Systematic), licence [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
