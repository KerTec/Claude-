# -*- coding: utf-8 -*-
"""
Ma collection de jeux – un « Pokédex » de jeux vidéo pour Pythonista (iPhone / iPad)

Consoles : PS2, N64, DS, 3DS, Xbox 360, Wii, GameCube, Switch.

Écrans :
  * Accueil : une carte par console (progression, jeux obtenus, valeur).
  * Console : grille de jaquettes numérotées. Obtenus = en couleur avec ✓,
    manquants = en gris. Rareté ★ à ★★★★★ et prix sur chaque case.
    Recherche, filtres (tous / obtenus / manquants), tri (n°, prix, rareté, A–Z),
    mode « Toucher : cocher » pour cocher très vite.
  * Fiche d'un jeu : grande jaquette, rareté, prix par condition, ventes récentes,
    « Je l'ai », mon prix, eBay, Leboncoin, PriceCharting.

Prix et jaquettes (automatique, sans clé API) :
  * Source : PriceCharting (versions PAL ; version US si le jeu n'est jamais sorti
    en Europe). Dollars convertis en euros au taux du jour.
  * Chargement en arrière-plan, un jeu à la fois (≈ 1 requête toutes les 4 s) :
    fiche ouverte d'abord, puis console affichée, puis jeux possédés, puis le reste.
    Premier lancement : ≈ 30 min pour tout le catalogue, ensuite gardé 30 jours.
  * Prix = cote PriceCharting ; fourchette = ventes eBay récentes.
  * Rareté = d'après la cote : Commun < 10 € ≤ Peu commun < 25 € ≤ Rare < 50 €
    ≤ Très rare < 100 € ≤ Légendaire.
  * Si le site bloque le script, bascule automatique sur un navigateur intégré.
  * Mauvais jeu trouvé ? Fiche du jeu > « Corriger la fiche ».

Fichiers (dans Documents/) :
  collection_jeux.json      jeux possédés, conditions, prix saisis, fiches corrigées
  prix_cache.json           prix déjà chargés
  jaquettes/                jaquettes téléchargées
  valeur_collection.csv     export de la valeur de la collection
  pricecharting_token.txt   clé API PriceCharting (facultative)
  journal_collection.txt    journal de bord (erreurs, événements)
  journal_plantages.txt     plantages durs de Pythonista
  debug_pricecharting.html  dernière page non reconnue (pour diagnostic)

Un problème ? Accueil > « Journal / signaler un problème » > « Copier le rapport »,
puis colle-le dans la conversation.
"""

import collections
import contextlib
import csv
import glob
import shutil
import functools
import hashlib
import html as htmllib
import json
import os
import random
import re
import sys
import threading
import time
import traceback
import unicodedata
import webbrowser
from urllib.parse import quote, quote_plus, urlencode

import console
import ui

# ====================================================================== réglages
DOCS = os.path.expanduser("~/Documents")
DATA_FILE = os.path.join(DOCS, "collection_jeux.json")
LEGACY_FILE = os.path.join(DOCS, "collection_ps2.json")
CACHE_FILE = os.path.join(DOCS, "prix_cache.json")
CSV_FILE = os.path.join(DOCS, "valeur_collection.csv")
DEBUG_FILE = os.path.join(DOCS, "debug_pricecharting.html")
TOKEN_FILE = os.path.join(DOCS, "pricecharting_token.txt")
COVER_DIR = os.path.join(DOCS, "jaquettes")
FULL_DIR = os.path.join(DOCS, "catalogue_complet")   # tous les jeux de chaque console
BACKUP_DIR = os.path.join(DOCS, "sauvegardes_collection")  # copies de sécurité
BACKUP_KEEP = 30            # nombre de sauvegardes gardées
BACKUP_EVERY = 3600         # sauvegarde automatique au plus toutes les heures

CACHE_VERSION = 3           # change si le format du cache change (l'ancien est ignoré)
CACHE_TTL = 30 * 24 * 3600  # un prix est gardé 30 jours (les cotes bougent peu)
BULK_PAGES = 4              # chargement rapide : pages « liste de la console » lues (150 jeux/page)
ERR_TTL = 6 * 3600          # jeu introuvable : nouvel essai automatique 6 h plus tard
RETRY_SOON = 5 * 60         # erreur passagère (réseau, anti-robot) : nouvel essai 5 min plus tard
MIN_GAP = 3.5               # au moins 3,5 s (+ 0 à 1,5 s au hasard) entre deux requêtes
BLOCK_PAUSE = 30 * 60       # pause si même le navigateur intégré est bloqué
WEB_TIMEOUT = 35            # délai max de chargement d'une page dans le navigateur intégré
DEFAULT_FX = 0.92           # taux USD→EUR de secours si hors ligne
BASE = "https://www.pricecharting.com"
# Page PriceCharting presque vide (recherche sans résultat) : la seule que le navigateur
# intégré affiche, pour passer la vérification. Les vraies pages sont téléchargées.
LIGHT_URL = BASE + "/search-products?type=prices&q=zzqxjw"

APP_VERSION = "3.30 (09/11/2026)"
UPDATE_URL = "https://raw.githubusercontent.com/KerTec/Claude-/main/collection_jeux.py"
LOG_FILE = os.path.join(DOCS, "journal_collection.txt")        # journal de bord
CRASH_FILE = os.path.join(DOCS, "journal_plantages.txt")      # plantages durs (faulthandler)
RUN_MARKER = os.path.join(DOCS, ".collection_session_en_cours")
JOB_FILE = os.path.join(DOCS, ".collection_chargement_en_cours")  # jeu en cours de chargement
STARTS_FILE = os.path.join(DOCS, ".collection_demarrages")        # plantages au démarrage
POISON_TTL = 7 * 24 * 3600  # jeu qui a fait planter l'app : mis de côté 7 jours
LOG_MAX = 400000            # au-delà, le journal est raccourci (on garde la fin)

# ====================================================================== catalogue
PS2 = [
    ("Les 15 indispensables", [
        "Grand Theft Auto: San Andreas", "Metal Gear Solid 3: Snake Eater",
        "Shadow of the Colossus", "Final Fantasy X", "Resident Evil 4",
        "God of War II", "Ōkami", "Grand Theft Auto: Vice City",
        "Metal Gear Solid 2: Sons of Liberty", "Gran Turismo 4",
        "Prince of Persia: The Sands of Time", "Burnout 3: Takedown",
        "Ratchet & Clank 3", "Kingdom Hearts II",
        "Devil May Cry 3: Dante’s Awakening"
    ]),
    ("Ratchet & Clank", [
        "Ratchet & Clank", "Ratchet & Clank 2: Going Commando",
        "Ratchet & Clank 3: Up Your Arsenal", "Ratchet: Gladiator"
    ]),
    ("Jak & Daxter", [
        "Jak and Daxter: The Precursor Legacy", "Jak II: Hors-la-loi",
        "Jak 3", "Jak X: Combat Racing"
    ]),
    ("Sly Cooper", [
        "Sly Raccoon", "Sly 2: Association de voleurs",
        "Sly 3: Honour Among Thieves"
    ]),
    ("Prince of Persia", [
        "Prince of Persia: The Sands of Time", "Prince of Persia: Warrior Within",
        "Prince of Persia: The Two Thrones"
    ]),
    ("God of War", ["God of War", "God of War II"]),
    ("Grand Theft Auto", [
        "Grand Theft Auto III", "Grand Theft Auto: Vice City",
        "Grand Theft Auto: San Andreas"
    ]),
    ("Metal Gear Solid", [
        "Metal Gear Solid 2: Sons of Liberty", "Metal Gear Solid 3: Snake Eater",
        "Metal Gear Solid 3: Subsistence"
    ]),
    ("Final Fantasy", ["Final Fantasy X", "Final Fantasy X-2", "Final Fantasy XII"]),
    ("Kingdom Hearts", ["Kingdom Hearts", "Kingdom Hearts II"]),
    ("Tony Hawk", [
        "Tony Hawk’s Pro Skater 3", "Tony Hawk’s Pro Skater 4",
        "Tony Hawk’s Underground", "Tony Hawk’s Underground 2"
    ]),
    ("RPG et jeux japonais", [
        "Dragon Quest VIII: L’Odyssée du roi maudit", "Persona 3", "Persona 4",
        "Rogue Galaxy", "Dark Cloud", "Dark Chronicle / Dark Cloud 2",
        "Suikoden V", "Odin Sphere", "Disgaea: Hour of Darkness",
        "Tales of the Abyss", "Tales of Legendia", "Valkyrie Profile 2: Silmeria",
        "Xenosaga Episode I", "Shin Megami Tensei: Nocturne / Lucifer’s Call"
    ]),
    ("Action, aventure et jeux cultes", [
        "ICO", "Beyond Good & Evil", "Bully / Canis Canem Edit", "The Warriors",
        "God Hand", "Viewtiful Joe", "Viewtiful Joe 2", "Klonoa 2: Lunatea’s Veil",
        "TimeSplitters 2", "TimeSplitters: Future Perfect", "Max Payne", "Max Payne 2",
        "The Simpsons: Hit & Run", "The Getaway", "The Getaway: Black Monday",
        "Onimusha: Warlords", "Onimusha 2: Samurai’s Destiny",
        "Onimusha 3: Demon Siege", "Legacy of Kain: Soul Reaver 2", "Primal",
        "Psychonauts", "Red Dead Revolver", "BLACK"
    ]),
    ("Horreur et survival", [
        "Silent Hill 2", "Silent Hill 3", "Silent Hill 4: The Room",
        "Resident Evil Code: Veronica X", "Resident Evil Outbreak",
        "Resident Evil Outbreak File #2", "Fatal Frame / Project Zero",
        "Fatal Frame II: Crimson Butterfly", "Fatal Frame III: The Tormented",
        "Haunting Ground", "Rule of Rose", "The Suffering",
        "The Suffering: Ties That Bind", "Obscure", "Obscure II"
    ]),
    ("Course, sport et sensations", [
        "Burnout", "Burnout 2: Point of Impact", "Burnout 3: Takedown",
        "Burnout Revenge", "Gran Turismo 3: A-Spec", "Gran Turismo 4",
        "Need for Speed: Underground", "Need for Speed: Underground 2",
        "Need for Speed: Most Wanted", "Need for Speed: Carbon", "SSX Tricky",
        "SSX 3", "Midnight Club 3: DUB Edition", "FlatOut 2", "Crazy Taxi",
        "Tourist Trophy", "Colin McRae Rally 04", "WRC 4"
    ]),
    ("Combat et multijoueur", [
        "Dragon Ball Z: Budokai", "Dragon Ball Z: Budokai 2",
        "Dragon Ball Z: Budokai 3", "Dragon Ball Z: Budokai Tenkaichi",
        "Dragon Ball Z: Budokai Tenkaichi 2", "Dragon Ball Z: Budokai Tenkaichi 3",
        "Tekken 4", "Tekken 5", "SoulCalibur II", "SoulCalibur III",
        "Def Jam: Fight for NY", "WWE SmackDown! Here Comes the Pain",
        "WWE SmackDown! vs. Raw 2006", "Virtua Fighter 4: Evolution",
        "Mortal Kombat: Shaolin Monks", "Star Wars: Battlefront",
        "Star Wars: Battlefront II", "Champions of Norrath",
        "Champions: Return to Arms", "LEGO Star Wars: The Video Game",
        "LEGO Star Wars II: The Original Trilogy", "Marvel: Ultimate Alliance"
    ]),
    ("FPS, guerre et infiltration", [
        "Medal of Honor: Frontline", "Medal of Honor: Rising Sun",
        "Call of Duty: Finest Hour", "Call of Duty 2: Big Red One", "Call of Duty 3",
        "Brothers in Arms: Road to Hill 30", "Brothers in Arms: Earned in Blood",
        "SOCOM II: U.S. Navy SEALs", "Tom Clancy’s Splinter Cell",
        "Splinter Cell: Pandora Tomorrow", "Splinter Cell: Chaos Theory",
        "Tom Clancy’s Ghost Recon", "007: Nightfire", "007: Everything or Nothing",
        "Red Faction", "Red Faction II", "The Mark of Kri", "Rogue Trooper"
    ]),
    ("Autres pépites", [
        "The Simpsons: Road Rage", "Katamari Damacy", "We Love Katamari",
        "The Lord of the Rings: The Two Towers",
        "The Lord of the Rings: The Return of the King",
        "The Lord of the Rings: The Third Age", "X-Men Legends",
        "X-Men Legends II: Rise of Apocalypse",
        "The Incredible Hulk: Ultimate Destruction", "Spider-Man 2",
        "Ultimate Spider-Man", "The Punisher", "Mafia",
        "Mercenaries: Playground of Destruction", "Scarface: The World Is Yours",
        "Manhunt", "Manhunt 2", "Ace Combat 04: Shattered Skies",
        "Ace Combat 5: The Unsung War", "Ace Combat Zero: The Belkan War",
        "Guitar Hero", "Guitar Hero II", "Guitar Hero III: Legends of Rock",
        "Frequency", "Amplitude"
    ])
]

N64 = [
    ("Top 7 N64", [
        "Super Mario 64", "The Legend of Zelda: Ocarina of Time",
        "The Legend of Zelda: Majora’s Mask", "GoldenEye 007", "Mario Kart 64",
        "Banjo-Kazooie", "Super Smash Bros."
    ]),
    ("Suites et séries N64", [
        "Banjo-Tooie", "Perfect Dark", "Mario Party 2", "Mario Party 3",
        "Paper Mario", "Star Fox 64", "Donkey Kong 64", "Conker’s Bad Fur Day",
        "Diddy Kong Racing", "F-Zero X", "Wave Race 64", "Pokémon Stadium",
        "Pokémon Stadium 2", "Pokémon Snap", "Yoshi’s Story",
        "Kirby 64: The Crystal Shards", "Mario Golf", "Mario Tennis",
        "Star Wars: Rogue Squadron", "Turok 2: Seeds of Evil"
    ])
]

DS = [
    ("Top 7 DS", [
        "New Super Mario Bros.", "Mario Kart DS", "Pokémon HeartGold / SoulSilver",
        "The Legend of Zelda: Phantom Hourglass",
        "Professor Layton and the Curious Village",
        "Animal Crossing: Wild World", "Phoenix Wright: Ace Attorney"
    ]),
    ("Suites : Zelda, Layton, Phoenix Wright", [
        "The Legend of Zelda: Spirit Tracks",
        "Professor Layton and the Diabolical Box",
        "Professor Layton and the Unwound Future",
        "Professor Layton and the Last Specter",
        "Phoenix Wright: Ace Attorney – Justice for All",
        "Phoenix Wright: Ace Attorney – Trials and Tribulations",
        "Apollo Justice: Ace Attorney",
        "Ace Attorney Investigations: Miles Edgeworth"
    ]),
    ("Suites : Pokémon et Mario", [
        "Pokémon Diamond / Pearl", "Pokémon Platinum", "Pokémon Black / White",
        "Pokémon Black 2 / White 2", "Super Mario 64 DS",
        "Mario & Luigi: Partners in Time", "Mario & Luigi: Bowser’s Inside Story",
        "Mario Party DS"
    ]),
    ("Autres incontournables DS", [
        "Castlevania: Dawn of Sorrow", "Castlevania: Portrait of Ruin",
        "Castlevania: Order of Ecclesia", "Advance Wars: Dual Strike",
        "Chrono Trigger", "Dragon Quest IX: Sentinels of the Starry Skies",
        "Kingdom Hearts 358/2 Days", "The World Ends with You",
        "Metroid Prime Hunters", "Ōkamiden",
        "Grand Theft Auto: Chinatown Wars"
    ])
]

DS3 = [
    ("Top 7 3DS", [
        "The Legend of Zelda: A Link Between Worlds", "Fire Emblem Awakening",
        "Pokémon X / Y", "Animal Crossing: New Leaf", "Super Mario 3D Land",
        "Monster Hunter 4 Ultimate", "Mario Kart 7"
    ]),
    ("Suites : Zelda, Fire Emblem, Monster Hunter", [
        "The Legend of Zelda: Ocarina of Time 3D",
        "The Legend of Zelda: Majora’s Mask 3D",
        "The Legend of Zelda: Tri Force Heroes",
        "Fire Emblem Fates", "Fire Emblem Echoes: Shadows of Valentia",
        "Monster Hunter Generations"
    ]),
    ("Suites : Pokémon et Mario", [
        "Pokémon Omega Ruby / Alpha Sapphire", "Pokémon Sun / Moon",
        "Pokémon Ultra Sun / Ultra Moon", "New Super Mario Bros. 2",
        "Luigi’s Mansion: Dark Moon", "Paper Mario: Sticker Star",
        "Mario & Luigi: Dream Team", "Super Smash Bros. for Nintendo 3DS"
    ]),
    ("Autres incontournables 3DS", [
        "Bravely Default", "Bravely Second: End Layer", "Kid Icarus: Uprising",
        "Xenoblade Chronicles 3D", "Kirby: Planet Robobot",
        "Metroid: Samus Returns", "Professor Layton and the Miracle Mask",
        "Professor Layton and the Azran Legacies", "Shin Megami Tensei IV",
        "Shin Megami Tensei IV: Apocalypse",
        "Dragon Quest VII: Fragments of the Forgotten Past", "Dragon Quest VIII",
        "Resident Evil: Revelations", "Etrian Odyssey IV",
        "Kingdom Hearts 3D: Dream Drop Distance"
    ])
]

X360 = [
    ("Top 7 Xbox 360", [
        "Halo 3", "Gears of War", "Mass Effect 2", "Red Dead Redemption",
        "BioShock", "The Elder Scrolls V: Skyrim",
        "Call of Duty 4: Modern Warfare"
    ]),
    ("Suites : Halo et Gears of War", [
        "Halo: Combat Evolved Anniversary", "Halo 3: ODST", "Halo: Reach",
        "Halo 4", "Gears of War 2", "Gears of War 3", "Gears of War: Judgment"
    ]),
    ("Suites : RPG occidentaux", [
        "Mass Effect", "Mass Effect 3", "The Elder Scrolls IV: Oblivion",
        "Fallout 3", "Fallout: New Vegas", "Fable II", "Fable III",
        "Borderlands", "Borderlands 2"
    ]),
    ("Suites : action et FPS", [
        "BioShock 2", "BioShock Infinite", "Call of Duty: Modern Warfare 2",
        "Call of Duty: Modern Warfare 3", "Call of Duty: Black Ops",
        "Call of Duty: Black Ops II", "Left 4 Dead", "Left 4 Dead 2",
        "Portal 2", "Dead Space", "Dead Space 2", "Dead Space 3"
    ]),
    ("Suites : aventure et monde ouvert", [
        "Grand Theft Auto IV", "Grand Theft Auto V", "Max Payne 3",
        "Assassin’s Creed II", "Assassin’s Creed: Brotherhood",
        "Assassin’s Creed: Revelations", "Assassin’s Creed III",
        "Batman: Arkham Asylum", "Batman: Arkham City", "Alan Wake"
    ]),
    ("Course et exclusivités", [
        "Forza Motorsport 3", "Forza Motorsport 4", "Forza Horizon",
        "Forza Horizon 2", "Lost Odyssey", "Blue Dragon", "Castle Crashers",
        "Limbo"
    ])
]

WII = [
    ("Top 7 Wii", [
        "Super Mario Galaxy", "The Legend of Zelda: Twilight Princess",
        "Super Smash Bros. Brawl", "Mario Kart Wii", "Xenoblade Chronicles",
        "Wii Sports", "New Super Mario Bros. Wii"
    ]),
    ("Suites des Top 7 Wii", [
        "Super Mario Galaxy 2", "Wii Sports Resort",
        "The Legend of Zelda: Skyward Sword", "Donkey Kong Country Returns",
        "Wii Fit", "Wii Fit Plus", "Mario Party 8", "Mario Party 9",
        "Super Paper Mario", "Mario Strikers Charged"
    ]),
    ("Metroid, Kirby et Nintendo", [
        "Metroid Prime Trilogy", "Metroid Prime 3: Corruption", "Metroid: Other M",
        "Kirby’s Epic Yarn", "Kirby’s Return to Dream Land", "Punch-Out!!",
        "Fire Emblem: Radiant Dawn", "Pikmin (New Play Control!)",
        "Pikmin 2 (New Play Control!)", "Super Mario All-Stars: 25th Anniversary"
    ]),
    ("RPG et cultes Wii", [
        "The Last Story", "Pandora’s Tower", "Ōkami", "Monster Hunter Tri",
        "Sin & Punishment: Star Successor", "No More Heroes",
        "No More Heroes 2: Desperate Struggle", "Sonic Colors",
        "Epic Mickey", "GoldenEye 007"
    ]),
    ("Horreur et tir Wii", [
        "Resident Evil 4: Wii Edition", "Resident Evil: The Umbrella Chronicles",
        "Resident Evil: The Darkside Chronicles",
        "Silent Hill: Shattered Memories"
    ])
]

GC = [
    ("Top 7 GameCube", [
        "The Legend of Zelda: The Wind Waker", "Metroid Prime",
        "Super Smash Bros. Melee", "Resident Evil 4",
        "Paper Mario: The Thousand-Year Door", "Super Mario Sunshine",
        "Mario Kart: Double Dash!!"
    ]),
    ("Suites des Top 7 GameCube", [
        "Metroid Prime 2: Echoes", "The Legend of Zelda: Twilight Princess",
        "The Legend of Zelda: Four Swords Adventures", "Resident Evil",
        "Resident Evil Zero", "Mario Party 4", "Mario Party 5", "Mario Party 6",
        "Mario Party 7"
    ]),
    ("Nintendo et séries cultes", [
        "Luigi’s Mansion", "Pikmin", "Pikmin 2", "Animal Crossing",
        "F-Zero GX", "Fire Emblem: Path of Radiance", "Star Fox Adventures",
        "Star Fox: Assault", "Super Mario Strikers",
        "Mario Golf: Toadstool Tour", "Mario Power Tennis",
        "Donkey Kong Jungle Beat", "Kirby Air Ride", "Wario World"
    ]),
    ("RPG, action et cultes", [
        "Metal Gear Solid: The Twin Snakes", "Tales of Symphonia",
        "Baten Kaitos: Eternal Wings and the Lost Ocean",
        "Skies of Arcadia Legends", "Eternal Darkness: Sanity’s Requiem",
        "killer7", "Viewtiful Joe", "SoulCalibur II", "Pokémon Colosseum",
        "Pokémon XD: Gale of Darkness", "Sonic Adventure 2: Battle"
    ])
]

SWITCH = [
    ("Top 7 Switch", [
        "The Legend of Zelda: Breath of the Wild", "Super Mario Odyssey",
        "Mario Kart 8 Deluxe", "Super Smash Bros. Ultimate",
        "Animal Crossing: New Horizons", "Metroid Dread",
        "Super Mario Bros. Wonder"
    ]),
    ("Suites : Zelda", [
        "The Legend of Zelda: Tears of the Kingdom",
        "The Legend of Zelda: Link’s Awakening",
        "The Legend of Zelda: Echoes of Wisdom"
    ]),
    ("Suites : Mario et Nintendo", [
        "Super Mario 3D World + Bowser’s Fury", "Super Mario Maker 2",
        "Super Mario Party", "Mario Party Superstars",
        "Super Mario Party Jamboree", "Paper Mario: The Origami King",
        "Paper Mario: The Thousand-Year Door", "Mario & Luigi: Brothership",
        "Luigi’s Mansion 3", "Donkey Kong Country: Tropical Freeze",
        "Kirby and the Forgotten Land", "Kirby Star Allies",
        "Metroid Prime Remastered"
    ]),
    ("Suites : Splatoon, Pikmin, Xenoblade, Fire Emblem", [
        "Splatoon 2", "Splatoon 3", "Pikmin 3 Deluxe", "Pikmin 4",
        "Xenoblade Chronicles: Definitive Edition", "Xenoblade Chronicles 2",
        "Xenoblade Chronicles 3", "Fire Emblem: Three Houses",
        "Fire Emblem Engage"
    ]),
    ("Pokémon sur Switch", [
        "Pokémon: Let’s Go, Pikachu! / Eevee!", "Pokémon Sword / Shield",
        "Pokémon Legends: Arceus", "Pokémon Scarlet / Violet"
    ]),
    ("Autres incontournables Switch", [
        "Bayonetta 2", "Bayonetta 3", "Astral Chain", "Octopath Traveler",
        "Dragon Quest XI S: Echoes of an Elusive Age", "Hades", "Hollow Knight",
        "Celeste", "Cuphead", "Stardew Valley"
    ])
]


PS3 = [
    ("Top 7 PS3", [
        "The Last of Us", "Uncharted 2: Among Thieves", "Red Dead Redemption",
        "Grand Theft Auto V", "Demon's Souls", "Metal Gear Solid 4: Guns of the Patriots",
        "God of War III"
    ]),
    ("Suites : Uncharted et God of War", [
        "Uncharted: Drake's Fortune", "Uncharted 3: Drake's Deception",
        "God of War Collection", "God of War: Ascension"
    ]),
    ("Suites : Batman, BioShock, Assassin's Creed", [
        "Batman: Arkham Asylum", "Batman: Arkham City", "BioShock", "BioShock Infinite",
        "Assassin's Creed II", "Assassin's Creed: Brotherhood", "Assassin's Creed IV: Black Flag"
    ]),
    ("Exclusivités et cultes PS3", [
        "LittleBigPlanet", "LittleBigPlanet 2", "Ratchet & Clank Future: Tools of Destruction",
        "Ratchet & Clank: A Crack in Time", "Killzone 2", "Killzone 3",
        "inFAMOUS", "inFAMOUS 2", "Heavy Rain", "Beyond: Two Souls",
        "Gran Turismo 5", "Gran Turismo 6", "Resistance: Fall of Man", "MotorStorm",
        "Ni no Kuni: Wrath of the White Witch", "Dark Souls", "Persona 5",
        "Valkyria Chronicles", "Journey Collector's Edition", "Skyrim"
    ]),
]

PS4 = [
    ("Top 7 PS4", [
        "Bloodborne", "God of War", "The Last of Us Part II", "Marvel's Spider-Man",
        "Horizon Zero Dawn", "Red Dead Redemption 2", "Uncharted 4: A Thief's End"
    ]),
    ("Suites : Spider-Man, Uncharted, The Last of Us", [
        "Marvel's Spider-Man: Miles Morales", "Uncharted: The Lost Legacy",
        "The Last of Us Remastered", "Uncharted: The Nathan Drake Collection"
    ]),
    ("Exclusivités PS4", [
        "Ghost of Tsushima", "Days Gone", "Death Stranding", "Detroit: Become Human",
        "Until Dawn", "Gran Turismo Sport", "Ratchet & Clank", "Persona 5 Royal",
        "Nioh", "Nioh 2", "Shadow of the Colossus", "Crash Bandicoot N. Sane Trilogy",
        "Spyro Reignited Trilogy"
    ]),
    ("Incontournables multi-plateformes", [
        "The Witcher 3: Wild Hunt", "Sekiro: Shadows Die Twice", "Dark Souls III",
        "Resident Evil 2", "Final Fantasy VII Remake", "Monster Hunter: World",
        "Grand Theft Auto V", "Elden Ring"
    ]),
]

PS5 = [
    ("Top 7 PS5", [
        "Elden Ring", "God of War Ragnarök", "Marvel's Spider-Man 2", "Astro Bot",
        "Demon's Souls", "Ratchet & Clank: Rift Apart", "Final Fantasy XVI"
    ]),
    ("Suites et remakes", [
        "Horizon Forbidden West", "Marvel's Spider-Man: Miles Morales",
        "The Last of Us Part I", "Final Fantasy VII Rebirth", "Resident Evil 4",
        "Ghost of Tsushima Director's Cut", "Gran Turismo 7"
    ]),
    ("Autres incontournables PS5", [
        "Returnal", "Stellar Blade", "Black Myth: Wukong", "Baldur's Gate 3",
        "Hogwarts Legacy", "Alan Wake 2", "Dragon's Dogma 2", "Metaphor: ReFantazio",
        "Silent Hill 2", "Sackboy: A Big Adventure"
    ]),
]

XBOX = [
    ("Top 7 Xbox", [
        "Halo: Combat Evolved", "Halo 2", "Star Wars: Knights of the Old Republic",
        "Fable", "Ninja Gaiden Black", "Project Gotham Racing 2", "Jade Empire"
    ]),
    ("Suites et séries Xbox", [
        "Star Wars: Knights of the Old Republic II", "Splinter Cell: Chaos Theory",
        "Forza Motorsport", "Conker: Live & Reloaded", "Ninja Gaiden",
        "Grand Theft Auto: San Andreas", "Burnout 3: Takedown"
    ]),
    ("Cultes Xbox", [
        "Jet Set Radio Future", "Panzer Dragoon Orta", "Psychonauts", "Fable: The Lost Chapters",
        "The Elder Scrolls III: Morrowind", "Max Payne 2", "Crimson Skies: High Road to Revenge",
        "Steel Battalion"
    ]),
]

XONE = [
    ("Top 7 Xbox One", [
        "Halo 5: Guardians", "Forza Horizon 4", "Gears 5", "Ori and the Will of the Wisps",
        "Halo: The Master Chief Collection", "Sea of Thieves", "Cuphead"
    ]),
    ("Suites : Forza, Gears, Halo", [
        "Forza Horizon 3", "Forza Motorsport 7", "Gears of War 4",
        "Gears of War: Ultimate Edition", "Halo Wars 2"
    ]),
    ("Exclusivités et cultes Xbox One", [
        "Ori and the Blind Forest: Definitive Edition", "Quantum Break", "Sunset Overdrive",
        "Titanfall", "Rare Replay", "State of Decay 2", "ReCore", "Ryse: Son of Rome",
        "The Witcher 3: Wild Hunt", "Red Dead Redemption 2"
    ]),
]

XSERIES = [
    ("Top 7 Xbox Series", [
        "Halo Infinite", "Forza Horizon 5", "Starfield", "Forza Motorsport",
        "Indiana Jones and the Great Circle", "Microsoft Flight Simulator", "Hi-Fi Rush"
    ]),
    ("Autres incontournables Xbox Series", [
        "Cyberpunk 2077", "Assassin's Creed Mirage", "Hogwarts Legacy", "Elden Ring",
        "Baldur's Gate 3", "Diablo IV", "Call of Duty: Black Ops 6", "Alan Wake 2",
        "Starfield Constellation Edition"
    ]),
]


NES = [
    ("Top 7 NES", [
        "Super Mario Bros. 3", "The Legend of Zelda", "Metroid", "Mega Man 2",
        "Castlevania", "Punch-Out!!", "Kirby's Adventure"
    ]),
    ("Suites et séries NES", [
        "Super Mario Bros.", "Super Mario Bros. 2", "Zelda II: The Adventure of Link",
        "Mega Man 3", "Castlevania III: Dracula's Curse", "Duck Tales", "Probotector / Contra",
        "Shadow Warriors / Ninja Gaiden", "Tetris", "Final Fantasy", "Bubble Bobble", "Double Dragon II"
    ]),
]

SNES = [
    ("Top 7 Super Nintendo", [
        "The Legend of Zelda: A Link to the Past", "Super Metroid", "Super Mario World",
        "Chrono Trigger", "Donkey Kong Country", "Super Mario Kart", "Street Fighter II"
    ]),
    ("Suites et séries Super Nintendo", [
        "Donkey Kong Country 2: Diddy's Kong Quest", "Donkey Kong Country 3",
        "Super Mario World 2: Yoshi's Island", "Super Mario All-Stars", "Super Mario RPG",
        "Final Fantasy VI", "Secret of Mana", "Kirby's Dream Land 3", "Starwing / Star Fox",
        "F-Zero", "Mega Man X", "Super Castlevania IV", "Super Probotector",
        "Earthbound", "Street Fighter II Turbo", "Killer Instinct"
    ]),
]

GB = [
    ("Top 7 Game Boy", [
        "Tetris", "Pokémon Red / Blue", "The Legend of Zelda: Link's Awakening",
        "Super Mario Land 2: 6 Golden Coins", "Kirby's Dream Land", "Metroid II: Return of Samus",
        "Wario Land: Super Mario Land 3"
    ]),
    ("Suites et séries Game Boy", [
        "Super Mario Land", "Pokémon Yellow", "Donkey Kong", "Donkey Kong Land",
        "Kirby's Dream Land 2", "Dr. Mario", "Mega Man: Dr. Wily's Revenge"
    ]),
]

GBC = [
    ("Top 7 Game Boy Color", [
        "Pokémon Gold / Silver", "Pokémon Crystal", "The Legend of Zelda: Oracle of Ages",
        "The Legend of Zelda: Oracle of Seasons", "Super Mario Bros. Deluxe",
        "The Legend of Zelda: Link's Awakening DX", "Wario Land 3"
    ]),
    ("Autres incontournables Game Boy Color", [
        "Pokémon Pinball", "Pokémon Trading Card Game", "Mario Tennis", "Mario Golf",
        "Shantae", "Dragon Warrior Monsters", "Metal Gear Solid"
    ]),
]

GBA = [
    ("Top 7 Game Boy Advance", [
        "Pokémon Emerald", "Metroid Fusion", "The Legend of Zelda: The Minish Cap",
        "Advance Wars", "Mario Kart: Super Circuit", "Golden Sun", "Castlevania: Aria of Sorrow"
    ]),
    ("Suites et séries Game Boy Advance", [
        "Pokémon Ruby / Sapphire", "Pokémon FireRed / LeafGreen", "Metroid: Zero Mission",
        "Advance Wars 2: Black Hole Rising", "Golden Sun: The Lost Age",
        "Mario & Luigi: Superstar Saga", "Fire Emblem", "Fire Emblem: The Sacred Stones",
        "Super Mario Advance 4: Super Mario Bros. 3", "Kirby & the Amazing Mirror",
        "WarioWare, Inc.: Minigame Mania", "The Legend of Zelda: A Link to the Past",
        "Final Fantasy Tactics Advance", "Castlevania: Harmony of Dissonance"
    ]),
]

MD = [
    ("Top 7 Mega Drive", [
        "Sonic the Hedgehog 2", "Streets of Rage 2", "Gunstar Heroes", "Sonic & Knuckles",
        "Phantasy Star IV", "Shining Force II", "Castlevania: The New Generation"
    ]),
    ("Suites et séries Mega Drive", [
        "Sonic the Hedgehog", "Sonic the Hedgehog 3", "Sonic Spinball", "Streets of Rage",
        "Streets of Rage 3", "Shining Force", "Golden Axe", "Ecco the Dolphin",
        "Mickey Mania", "Aladdin", "The Lion King", "Earthworm Jim", "ToeJam & Earl",
        "Comix Zone", "Shinobi III: Return of the Ninja Master"
    ]),
]

MS = [
    ("Top 7 Master System", [
        "Alex Kidd in Miracle World", "Sonic the Hedgehog", "Phantasy Star",
        "Wonder Boy III: The Dragon's Trap", "Castle of Illusion", "Psycho Fox", "R-Type"
    ]),
    ("Autres incontournables Master System", [
        "Sonic the Hedgehog 2", "Golden Axe Warrior", "Land of Illusion", "Asterix",
        "Shinobi", "OutRun", "Master of Darkness"
    ]),
]

GG = [
    ("Top 7 Game Gear", [
        "Sonic the Hedgehog", "Sonic the Hedgehog 2", "Shinobi", "Columns",
        "Sonic Triple Trouble", "The GG Shinobi II: The Silent Fury", "Sonic Chaos"
    ]),
]

PS1 = [
    ("Top 7 PlayStation", [
        "Final Fantasy VII", "Metal Gear Solid", "Castlevania: Symphony of the Night",
        "Crash Bandicoot", "Gran Turismo", "Resident Evil 2", "Tekken 3"
    ]),
    ("Suites et séries PlayStation", [
        "Crash Bandicoot 2: Cortex Strikes Back", "Crash Bandicoot 3: Warped", "Crash Team Racing",
        "Spyro the Dragon", "Spyro 2: Gateway to Glimmer", "Spyro: Year of the Dragon",
        "Final Fantasy VIII", "Final Fantasy IX", "Gran Turismo 2", "Resident Evil",
        "Resident Evil 3: Nemesis", "Tomb Raider", "Tony Hawk's Pro Skater 2",
        "Silent Hill", "Chrono Cross", "Oddworld: Abe's Oddysee", "Medievil", "Ape Escape",
        "Vagrant Story", "Driver"
    ]),
]

SATURN = [
    ("Top 7 Saturn", [
        "Panzer Dragoon Saga", "NiGHTS into Dreams", "Guardian Heroes", "Sega Rally Championship",
        "Virtua Fighter 2", "Saturn Bomberman", "Virtua Cop"
    ]),
    ("Autres incontournables Saturn", [
        "Panzer Dragoon", "Panzer Dragoon II Zwei", "Daytona USA", "Sonic Jam",
        "Burning Rangers", "Dragon Force", "Fighters Megamix"
    ]),
]

DREAMCAST = [
    ("Top 7 Dreamcast", [
        "Shenmue", "Jet Set Radio", "Soulcalibur", "Crazy Taxi", "Sonic Adventure",
        "Skies of Arcadia", "Power Stone 2"
    ]),
    ("Autres incontournables Dreamcast", [
        "Shenmue II", "Sonic Adventure 2", "Resident Evil Code: Veronica", "Rez",
        "Marvel vs. Capcom 2", "Virtua Tennis", "Phantasy Star Online", "Metropolis Street Racer",
        "Space Channel 5", "Samba de Amigo"
    ]),
]


SWITCH2 = [
    ("Top 7 Switch 2", [
        "Mario Kart World", "Donkey Kong Bananza", "Pokémon Legends: Z-A",
        "Metroid Prime 4: Beyond", "Kirby Air Riders", "Hyrule Warriors: Age of Imprisonment",
        "The Legend of Zelda: Tears of the Kingdom (Switch 2)"
    ]),
    ("Éditions Nintendo Switch 2", [
        "The Legend of Zelda: Breath of the Wild - Nintendo Switch 2 Edition",
        "Kirby and the Forgotten Land + Star-Crossed World",
        "Super Mario Party Jamboree + Jamboree TV", "Fire Emblem: Fortune's Weave",
        "Yoshi and the Mysterious Book", "Mario Tennis Fever", "Splatoon Raiders",
        "Pokémon Pokopia", "Star Fox"
    ]),
    ("Autres incontournables Switch 2", [
        "Cyberpunk 2077: Ultimate Edition", "Elden Ring: Tarnished Edition",
        "Final Fantasy VII Remake Intergrade", "Final Fantasy VII Rebirth",
        "Indiana Jones and the Great Circle", "Hades II", "Resident Evil Requiem",
        "Street Fighter 6: Years 1-2 Fighters Edition", "Dragon Quest I & II HD-2D Remake",
        "Star Wars Outlaws",
        "Assassin's Creed Shadows", "Sonic X Shadow Generations"
    ]),
]

# (étiquette courte, nom complet, sections, slug PriceCharting, nom console PriceCharting)
CONSOLES = [
    ("PS2", "PlayStation 2", PS2, "pal-playstation-2", "PAL Playstation 2"),
    ("N64", "Nintendo 64", N64, "pal-nintendo-64", "PAL Nintendo 64"),
    ("DS", "Nintendo DS", DS, "pal-nintendo-ds", "PAL Nintendo DS"),
    ("3DS", "Nintendo 3DS", DS3, "pal-nintendo-3ds", "PAL Nintendo 3DS"),
    ("360", "Xbox 360", X360, "pal-xbox-360", "PAL Xbox 360"),
    ("Wii", "Wii", WII, "pal-wii", "PAL Wii"),
    ("GC", "GameCube", GC, "pal-gamecube", "PAL Gamecube"),
    ("Switch", "Nintendo Switch", SWITCH, "pal-nintendo-switch", "PAL Nintendo Switch"),
    ("Switch2", "Nintendo Switch 2", SWITCH2, "pal-nintendo-switch-2", "PAL Nintendo Switch 2"),
    ("PS3", "PlayStation 3", PS3, "pal-playstation-3", "PAL Playstation 3"),
    ("PS4", "PlayStation 4", PS4, "pal-playstation-4", "PAL Playstation 4"),
    ("PS5", "PlayStation 5", PS5, "pal-playstation-5", "PAL Playstation 5"),
    ("Xbox", "Xbox", XBOX, "pal-xbox", "PAL Xbox"),
    ("One", "Xbox One", XONE, "pal-xbox-one", "PAL Xbox One"),
    ("Series", "Xbox Series X", XSERIES, "pal-xbox-series-x", "PAL Xbox Series X"),
    ("NES", "NES", NES, "pal-nes", "PAL NES"),
    ("SNES", "Super Nintendo", SNES, "pal-super-nintendo", "PAL Super Nintendo"),
    ("GB", "Game Boy", GB, "pal-gameboy", "PAL GameBoy"),
    ("GBC", "Game Boy Color", GBC, "pal-gameboy-color", "PAL GameBoy Color"),
    ("GBA", "Game Boy Advance", GBA, "pal-gameboy-advance", "PAL GameBoy Advance"),
    ("MD", "Mega Drive", MD, "pal-sega-mega-drive", "PAL Sega Mega Drive"),
    ("MS", "Master System", MS, "pal-sega-master-system", "PAL Sega Master System"),
    ("GG", "Game Gear", GG, "pal-sega-game-gear", "PAL Sega Game Gear"),
    ("PS1", "PlayStation", PS1, "pal-playstation", "PAL Playstation"),
    ("Saturn", "Saturn", SATURN, "pal-sega-saturn", "PAL Sega Saturn"),
    ("DC", "Dreamcast", DREAMCAST, "pal-sega-dreamcast", "PAL Sega Dreamcast"),
]

# Images des consoles de RetroArch (thème XMB « Systematic »), dépôt libretro/retroarch-assets,
# licence Creative Commons BY 4.0 (auteurs : équipe libretro / contributeurs RetroArch).
RA_ICON_BASE = "https://raw.githubusercontent.com/libretro/retroarch-assets/master/xmb/systematic/png/"
RA_ICONS = {
    "NES": "Nintendo - Nintendo Entertainment System",
    "SNES": "Nintendo - Super Nintendo Entertainment System",
    "GB": "Nintendo - Game Boy", "GBC": "Nintendo - Game Boy Color",
    "GBA": "Nintendo - Game Boy Advance", "N64": "Nintendo - Nintendo 64",
    "GC": "Nintendo - GameCube", "Wii": "Nintendo - Wii", "Switch": "Nintendo - Switch",
    "Switch2": "Nintendo - Switch 2", "DS": "Nintendo - Nintendo DS",
    "3DS": "Nintendo - Nintendo 3DS", "MS": "Sega - Master System - Mark III",
    "MD": "Sega - Mega Drive - Genesis", "GG": "Sega - Game Gear", "Saturn": "Sega - Saturn",
    "DC": "Sega - Dreamcast", "PS1": "Sony - PlayStation", "PS2": "Sony - PlayStation 2",
    "PS3": "Sony - PlayStation 3 (PSN)", "PS4": "Sony - PlayStation 4",
    "PS5": "Sony - PlayStation 5",
    "Xbox": "Microsoft - Xbox", "360": "Microsoft - Xbox 360", "One": "Microsoft - Xbox One",
    "Series": "Microsoft - Xbox Series X",
}
RA_CREDIT = ("Images des consoles : RetroArch / libretro (retroarch-assets, thème Systematic), "
             "licence CC BY 4.0")

# Couleur de chaque famille (sélecteur de consoles).
FAMILY_COLORS = {"Rétro 2D": "#8e44ad", "Nintendo": "#e60012", "PlayStation": "#0070d1",
                 "Sega": "#1e5bc6", "Xbox": "#107c10"}
# Familles affichées sur l'accueil (ordre d'affichage).
FAMILIES = [
    ("Rétro 2D", ["NES", "SNES", "GB", "GBC", "GBA", "MS", "MD", "GG"]),
    ("Nintendo", ["N64", "GC", "Wii", "Switch", "Switch2", "DS", "3DS"]),
    ("PlayStation", ["PS1", "PS2", "PS3", "PS4", "PS5"]),
    ("Sega", ["Saturn", "DC"]),
    ("Xbox", ["Xbox", "360", "One", "Series"]),
]
LABELS = [c[0] for c in CONSOLES]
FULL_NAME = {c[0]: c[1] for c in CONSOLES}
SECTIONS_BY = {c[0]: c[2] for c in CONSOLES}
PC = {c[0]: (c[3], c[4]) for c in CONSOLES}
# Un jeu présent dans plusieurs sections d'une même console ne compte qu'une fois.
GAMES_BY = {
    c[0]: list(dict.fromkeys(g for _, games in c[2] for g in games)) for c in CONSOLES
}
SEL_SET = {l: set(g) for l, g in GAMES_BY.items()}

# Noms à chercher sur PriceCharting quand le titre du catalogue est en français
# ou différent du titre PAL anglais utilisé par le site.
SEARCH_ALIASES = {
    "Jak II: Hors-la-loi": "Jak II: Renegade",
    "Sly 2: Association de voleurs": "Sly 2: Band of Thieves",
    "Dragon Quest VIII: L’Odyssée du roi maudit": "Dragon Quest VIII: Journey of the Cursed King",
    "Tony Hawk’s Pro Skater 3": "Tony Hawk 3",
    "Tony Hawk’s Pro Skater 4": "Tony Hawk 4",
    "Fatal Frame / Project Zero": "Project Zero",
    "Fatal Frame II: Crimson Butterfly": "Project Zero 2",
    "Fatal Frame III: The Tormented": "Project Zero 3",
    "Bully / Canis Canem Edit": "Canis Canem Edit / Bully",
    "Ace Combat 04: Shattered Skies": "Ace Combat: Distant Thunder",
    "Ace Combat 5: The Unsung War": "Ace Combat: Squadron Leader",
    "Ace Combat Zero: The Belkan War": "Ace Combat: The Belkan War",
    "Star Fox 64": "Lylat Wars",
    "Xenosaga Episode I": "Xenosaga",
    "Skyrim": "The Elder Scrolls V: Skyrim",
    "Final Fantasy VI": "Final Fantasy III",
    "Tony Hawk's Pro Skater 2": "Tony Hawk's Skateboarding 2",
    "Marvel's Spider-Man": "Marvel Spiderman",
    "Professor Layton and the Diabolical Box": "Professor Layton and Pandora's Box",
    "Professor Layton and the Unwound Future": "Professor Layton and the Lost Future",
    "Professor Layton and the Azran Legacies": "Professor Layton and the Azran Legacy",
    "Luigi’s Mansion: Dark Moon": "Luigi's Mansion 2",
    "Kirby’s Return to Dream Land": "Kirby's Adventure Wii",
    "Pikmin (New Play Control!)": "New Play Control: Pikmin",
    "Pikmin 2 (New Play Control!)": "New Play Control: Pikmin 2",
    "Sonic Colors": "Sonic Colours",
    "Super Mario Strikers": "Mario Smash Football",
}

# Nom de la console sur PriceCharting pour la version US (jeux jamais sortis en Europe).
US_PC = {
    "PS2": ("playstation-2", "Playstation 2"),
    "N64": ("nintendo-64", "Nintendo 64"),
    "DS": ("nintendo-ds", "Nintendo DS"),
    "3DS": ("nintendo-3ds", "Nintendo 3DS"),
    "360": ("xbox-360", "Xbox 360"),
    "Wii": ("wii", "Wii"),
    "GC": ("gamecube", "Gamecube"),
    "Switch": ("nintendo-switch", "Nintendo Switch"),
    "Switch2": ("nintendo-switch-2", "Nintendo Switch 2"),
    "PS3": ("playstation-3", "Playstation 3"),
    "PS4": ("playstation-4", "Playstation 4"),
    "PS5": ("playstation-5", "Playstation 5"),
    "Xbox": ("xbox", "Xbox"),
    "One": ("xbox-one", "Xbox One"),
    "Series": ("xbox-series-x", "Xbox Series X"),
    "NES": ("nes", "NES"), "SNES": ("super-nintendo", "Super Nintendo"),
    "GB": ("gameboy", "GameBoy"), "GBC": ("gameboy-color", "GameBoy Color"),
    "GBA": ("gameboy-advance", "GameBoy Advance"), "MD": ("sega-genesis", "Sega Genesis"),
    "MS": ("sega-master-system", "Sega Master System"), "GG": ("sega-game-gear", "Sega Game Gear"),
    "PS1": ("playstation", "Playstation"), "Saturn": ("sega-saturn", "Sega Saturn"),
    "DC": ("sega-dreamcast", "Sega Dreamcast"),
}

# condition : (id de la cote sur la page du jeu, bloc des ventes, champ API, colonne recherche)
COND = {
    "Disque seul": ("used_price", "used", "loose-price", "used_price"),
    "Complet": ("complete_price", "cib", "cib-price", "cib_price"),
    "Neuf": ("new_price", "new", "new-price", "new_price"),
}
DEFAULT_COND = "Disque seul"


# ====================================================================== utilitaires
def key_of(label, game):
    return "%s|%s" % (label, game)


def read_json(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError, TypeError):
        return None


def write_json(path, data, **kw):
    """Écriture atomique : le fichier n'est jamais à moitié écrit."""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, **kw)
    os.replace(tmp, path)


def strip_accents(text):
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c))


_NORM = {}


def normalize(text):
    """Pour la recherche : « okami » trouve « Ōkami », « pokemon » trouve « Pokémon ».
    Résultat gardé en mémoire (recherche instantanée sur des milliers de jeux)."""
    r = _NORM.get(text)
    if r is None:
        r = strip_accents(text.replace("’", "'")).casefold()
        if len(_NORM) < 50000:
            _NORM[text] = r
    return r


def search_name(game):
    """Nom à envoyer aux sites : alias éventuel, sans parenthèses,
    premier titre de « X / Y », sans accents."""
    g = SEARCH_ALIASES.get(game, game)
    g = re.sub(r"\s*\(.*?\)", "", g).split(" / ")[0]
    g = g.replace("’", "'").replace("–", "-")
    return strip_accents(g).strip()


def eur(x):
    """1234.5 -> « 1 234,50 € »"""
    return "{:,.2f} €".format(x).replace(",", " ").replace(".", ",")


def eur_short(x):
    """Montant arrondi pour la liste : « 18 € », « 1 234 € »."""
    return "{:,.0f} €".format(x).replace(",", " ")


def plural(n, word):
    return "%d %s%s" % (n, word, "s" if n > 1 else "")


def parse_euros(text):
    t = (text or "").replace("€", "").replace(" ", "").replace(" ", "").replace(",", ".")
    v = float(t)
    if v < 0:
        raise ValueError("négatif")
    return round(v, 2)


def quantile(sorted_values, q):
    """Quantile par interpolation linéaire sur une liste déjà triée."""
    n = len(sorted_values)
    if n == 1:
        return sorted_values[0]
    pos = (n - 1) * q
    lo = int(pos)
    hi = min(lo + 1, n - 1)
    return sorted_values[lo] + (sorted_values[hi] - sorted_values[lo]) * (pos - lo)


def read_token():
    try:
        with open(TOKEN_FILE, "r", encoding="utf-8") as f:
            return f.read().strip() or None
    except OSError:
        return None


def write_token(token):
    if token:
        with open(TOKEN_FILE, "w", encoding="utf-8") as f:
            f.write(token)
    elif os.path.exists(TOKEN_FILE):
        os.remove(TOKEN_FILE)


def save_debug(page):
    try:
        with open(DEBUG_FILE, "w", encoding="utf-8") as f:
            f.write(page or "")
    except OSError:
        pass


def alert(title, message):
    """Boîte de dialogue bloquante : à appeler HORS du fil principal de l'interface."""
    try:
        console.alert(title, message, "OK", hide_cancel_button=True)
    except KeyboardInterrupt:
        pass


_HUD_BUSY = [False]


def hud(message, icon="success", duration=1.0):
    """Petite bulle de confirmation. Toujours affichée depuis un fil séparé :
    console.hud_alert « bloque jusqu'à ce que la bulle disparaisse » (doc Pythonista),
    appelée depuis l'interface elle la gèlerait. Une seule bulle à la fois."""
    if _HUD_BUSY[0] and icon != "error":
        return
    _HUD_BUSY[0] = True

    def show():
        try:
            console.hud_alert(message, icon, max(0.25, min(duration, 5.0)))
        except Exception:
            pass
        finally:
            _HUD_BUSY[0] = False
    t = threading.Thread(target=show, name="bulle")
    t.daemon = True
    t.start()


def run_thread(fn, *args):
    t = threading.Thread(target=fn, args=args)
    t.daemon = True
    t.start()
    return t


# Boîte aux lettres vers l'interface. Les tâches de fond n'appellent JAMAIS ui.* :
# elles déposent ici, et la fenêtre principale relève la boîte 4 fois par seconde
# (update_interval), sur le fil de l'interface. Appeler ui.delay depuis un fil de fond
# fait planter Pythonista (« Aborted » / « Segmentation fault »).
_MAIN_QUEUE = collections.deque()


def on_main(fn, *args):
    """Exécute fn sur le fil de l'interface (au prochain relevé, < 0,3 s)."""
    _MAIN_QUEUE.append((fn, args))


def drain_main_queue(limit=40):
    """Appelée uniquement par la fenêtre principale (fil de l'interface)."""
    n = 0
    while _MAIN_QUEUE and n < limit:
        fn, args = _MAIN_QUEUE.popleft()
        guard(fn)(*args)
        n += 1


# ====================================================================== journal de bord
_LOG_LOCK = threading.Lock()
_LAST_ERROR_HUD = [0.0]
_CRASH_FH = []


def log(message, level="INFO"):
    """Ajoute une ligne datée au journal (Documents/journal_collection.txt)."""
    name = threading.current_thread().name
    line = "%s [%s] %-6s %s\n" % (time.strftime("%d/%m %H:%M:%S"),
                                   "ui" if name == "MainThread" else name[:10], level, message)
    with _LOG_LOCK:
        try:
            if os.path.exists(LOG_FILE) and os.path.getsize(LOG_FILE) > LOG_MAX:
                with open(LOG_FILE, "r", encoding="utf-8", errors="replace") as f:
                    keep = f.read()[-LOG_MAX // 2:]
                keep = keep[keep.find("\n") + 1:]
                with open(LOG_FILE + ".tmp", "w", encoding="utf-8") as f:
                    f.write("[... début du journal supprimé ...]\n" + keep)
                os.replace(LOG_FILE + ".tmp", LOG_FILE)
            with open(LOG_FILE, "a", encoding="utf-8") as f:
                f.write(line)
        except OSError:
            pass


def log_exception(where):
    log("%s\n%s" % (where, traceback.format_exc().rstrip()), "ERREUR")


def guard(fn):
    """Enveloppe : une erreur est enregistrée dans le journal au lieu de tout planter."""
    if getattr(fn, "_guarded", False):
        return fn

    @functools.wraps(fn)
    def wrapper(*args, **kwargs):
        try:
            return fn(*args, **kwargs)
        except KeyboardInterrupt:      # « Annuler » dans une boîte de dialogue
            return None
        except Exception:
            log_exception("Erreur dans %s" % getattr(fn, "__qualname__", fn))
            if time.time() - _LAST_ERROR_HUD[0] > 8:
                _LAST_ERROR_HUD[0] = time.time()
                hud("Problème enregistré dans le journal", "error", 1.5)
            return None
    wrapper._guarded = True
    return wrapper


def guard_class(cls):
    """Protège toutes les méthodes d'une vue (sauf __init__)."""
    for name, value in list(vars(cls).items()):
        if name.startswith("__") or isinstance(value, (staticmethod, classmethod, type)):
            continue
        if callable(value):
            setattr(cls, name, guard(value))
    return cls


def background(fn):
    """Comme ui.in_background, mais les erreurs vont dans le journal."""
    return ui.in_background(guard(fn))


def install_crash_handlers():
    """Erreurs non attrapées (tous les fils) + plantages durs de Python."""
    def hook(exc_type, exc, tb):
        log("Exception non gérée :\n" + "".join(
            traceback.format_exception(exc_type, exc, tb)).rstrip(), "CRASH")
    previous = sys.excepthook

    def excepthook(exc_type, exc, tb):
        hook(exc_type, exc, tb)
        try:
            previous(exc_type, exc, tb)
        except Exception:
            pass
    if not getattr(sys.excepthook, "_collection", False):  # pas de double journalisation
        excepthook._collection = True
        sys.excepthook = excepthook
    if hasattr(threading, "excepthook"):
        threading.excepthook = lambda a: hook(a.exc_type, a.exc_value, a.exc_traceback)
    try:
        import faulthandler
        if not _CRASH_FH:
            fh = open(CRASH_FILE, "a", encoding="utf-8")
            fh.write("\n--- session du %s ---\n" % time.strftime("%d/%m/%Y %H:%M:%S"))
            fh.flush()
            _CRASH_FH.append(fh)
            faulthandler.enable(fh, all_threads=True)
    except Exception:
        pass


def crash_text():
    """Plantages durs enregistrés (seulement les sessions qui contiennent une trace)."""
    try:
        with open(CRASH_FILE, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return ""
    parts = [p for p in text.split("\n--- session du ") if "File " in p or "Fatal" in p]
    return "\n--- session du ".join(parts[-3:]).strip()


def run_named(name, fn, *args):
    t = threading.Thread(target=guard(fn), args=args, name=name)
    t.daemon = True
    t.start()
    return t


# ====================================================================== mise à jour
def version_tuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", (v or "").split("(")[0])[:3])


def check_update():
    """(version, code) si une version plus récente est publiée, sinon None."""
    import requests
    r = requests.get(UPDATE_URL, params={"t": int(time.time())}, timeout=20)
    if r.status_code != 200:
        raise IOError("HTTP %d" % r.status_code)
    m = re.search(r'^APP_VERSION = "([^"]+)"', r.text, re.M)
    if not m:
        raise IOError("fichier de mise à jour illisible")
    if version_tuple(m.group(1)) > version_tuple(APP_VERSION):
        return m.group(1), r.text
    return None


def script_path():
    """Emplacement de ce script (Pythonista ne définit pas toujours __file__)."""
    candidates = []
    if sys.argv and sys.argv[0]:
        candidates.append(sys.argv[0])
    try:
        candidates.append(__file__)
    except NameError:
        pass
    for p in candidates:
        p = os.path.abspath(p)
        if p.endswith(".py") and os.path.exists(p):
            return p
    return os.path.join(DOCS, "collection_jeux.py")


def install_update(code):
    """Remplace ce script par la nouvelle version (vérifiée avant d'écrire).
    La collection n'est pas touchée, mais on en fait une copie de sécurité avant."""
    compile(code, "collection_jeux.py", "exec")  # refuse un fichier abîmé
    backup_collection("avant-mise-a-jour")
    path = script_path()
    log("Installation de la mise à jour dans %s" % path)
    tmp = path + ".maj"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(code)
    os.replace(tmp, path)
    return path


# ====================================================================== sauvegardes
def is_collection(data):
    return isinstance(data, dict) and any(k in data for k in LABELS)


def collection_size(data):
    return sum(len(v) for k, v in data.items() if k in LABELS and isinstance(v, list))


def read_collection_file(path):
    """Lit un fichier de collection ; 3 essais (une lecture peut échouer un instant)."""
    for _ in range(3):
        data = read_json(path)
        if is_collection(data):
            return data
        if not os.path.exists(path):
            return None
        time.sleep(0.2)
    return None


def list_backups():
    """[(chemin, date, nombre de jeux, raison)] du plus récent au plus ancien."""
    out = []
    for p in glob.glob(os.path.join(BACKUP_DIR, "collection_*.json")):
        data = read_json(p)
        if not is_collection(data):
            continue
        reason = os.path.basename(p)[len("collection_") + 16:-5].strip("_") or "auto"
        out.append((p, os.path.getmtime(p), collection_size(data), reason))
    out.sort(key=lambda b: b[1], reverse=True)
    return out


def backup_collection(reason):
    """Copie datée de collection_jeux.json (si elle diffère de la dernière copie)."""
    current = read_json(DATA_FILE) if os.path.exists(DATA_FILE) else None
    if not is_collection(current) or collection_size(current) == 0:
        return None                               # rien d'utile à sauvegarder
    try:
        os.makedirs(BACKUP_DIR, exist_ok=True)
        with open(DATA_FILE, "rb") as f:
            content = f.read()
        backups = list_backups()
        if backups:
            with open(backups[0][0], "rb") as f:
                if f.read() == content:
                    return backups[0][0]          # rien n'a changé depuis
        path = os.path.join(BACKUP_DIR, "collection_%s_%s.json"
                            % (time.strftime("%Y%m%d-%H%M%S"), re.sub(r"\W+", "-", reason)))
        with open(path, "wb") as f:
            f.write(content)
        backups = list_backups()
        biggest = max(backups, key=lambda b: b[2])[0] if backups else None
        for old in backups[BACKUP_KEEP:]:
            if old[0] != biggest:                 # la plus complète est toujours gardée
                os.remove(old[0])
        log("Sauvegarde de la collection (%s) : %s" % (reason, os.path.basename(path)))
        return path
    except OSError as e:
        log("Sauvegarde de la collection impossible : %s" % e, "ERREUR")
        return None


# ====================================================================== collection
class Collection:
    """Jeux possédés, condition par jeu, prix saisis à la main, fiches corrigées."""

    def __init__(self):
        self.lock = threading.RLock()
        self.owned = {label: set() for label in LABELS}
        self.conditions = {}
        self.manual = {}
        self.urls = {}  # fiche PriceCharting choisie à la main : "PS2|jeu" -> url
        self.added = {}  # "PS2|jeu" -> {"ts": date d'ajout, "p": prix (€) à cette date}
        self.source = "fichier"
        self.last_backup = 0.0
        self.load()

    def reload(self):
        with self.lock:
            self.owned = {label: set() for label in LABELS}
            self.conditions, self.manual, self.urls, self.added = {}, {}, {}, {}
            self.load()

    def load(self):
        """Charge la collection. Ne l'écrase JAMAIS : si le fichier est illisible, il est
        mis de côté et la dernière sauvegarde est rechargée à la place."""
        data = read_collection_file(DATA_FILE)
        self.source = "fichier"
        if data is None and os.path.exists(DATA_FILE):
            kept = DATA_FILE.replace(".json", "_illisible_%s.json" % time.strftime("%Y%m%d-%H%M%S"))
            try:
                shutil.copy2(DATA_FILE, kept)
            except OSError:
                pass
            log("Fichier de collection illisible, mis de côté : %s" % os.path.basename(kept),
                "ALERTE")
        if data is None:
            for path, _, count, _ in list_backups():
                data = read_collection_file(path)
                if data is not None:
                    self.source = "sauvegarde %s" % os.path.basename(path)
                    log("Collection rechargée depuis la sauvegarde %s (%d jeux)"
                        % (os.path.basename(path), count), "ALERTE")
                    break
        if data is not None:
            self.apply(data)
            log("Collection chargée (%s) : %d jeux" % (self.source, self.total()))
            if self.source != "fichier":
                self.save()       # remet la sauvegarde en place comme fichier principal
            return
        # Vraiment aucune collection (ni fichier ni sauvegarde) : premier lancement.
        legacy = read_json(LEGACY_FILE)  # ancienne version (PS2 seule)
        if isinstance(legacy, list):
            self.owned["PS2"].update(g for g in legacy if isinstance(g, str))
            self.source = "ancienne version (collection_ps2.json)"
        else:
            self.owned["PS2"].add("BLACK")  # premier lancement : BLACK déjà possédé
            self.source = "nouvelle collection"
        log("Collection créée (%s) : %d jeux" % (self.source, self.total()), "ALERTE")
        self.save()

    def total(self):
        return sum(len(v) for v in self.owned.values())

    def apply(self, data):
        """Applique le contenu d'un fichier de collection."""
        for label in LABELS:
            items = data.get(label)
            if isinstance(items, list):
                self.owned[label].update(g for g in items if isinstance(g, str))
        conds = data.get("_conditions")
        if isinstance(conds, dict):
            self.conditions = {k: v for k, v in conds.items()
                               if isinstance(k, str) and v in COND}
        manual = data.get("_manual")
        if isinstance(manual, dict):
            self.manual = {k: float(v) for k, v in manual.items()
                           if isinstance(k, str) and isinstance(v, (int, float))
                           and not isinstance(v, bool) and v >= 0}
        added = data.get("_added")
        if isinstance(added, dict):
            self.added = {k: v for k, v in added.items()
                          if isinstance(k, str) and isinstance(v, dict)}
        urls = data.get("_urls")
        if isinstance(urls, dict):
            self.urls = {k: v for k, v in urls.items()
                         if isinstance(k, str) and isinstance(v, str) and "/game/" in v}

    def save(self):
        """Renvoie None si tout va bien, sinon le message d'erreur."""
        with self.lock:
            payload = {k: sorted(v) for k, v in self.owned.items()}
            payload["_conditions"] = dict(self.conditions)
            payload["_manual"] = dict(self.manual)
            payload["_urls"] = dict(self.urls)
            payload["_added"] = dict(self.added)
            try:
                write_json(DATA_FILE, payload, indent=2)
            except OSError as e:
                log("Sauvegarde de la collection impossible : %s" % e, "ERREUR")
                return str(e)
        if time.time() - self.last_backup > BACKUP_EVERY:   # copie de sécurité horaire
            self.last_backup = time.time()
            backup_collection("auto")
        return None

    def is_owned(self, label, game):
        return game in self.owned[label]

    def toggle(self, label, game):
        with self.lock:
            s = self.owned[label]
            if game in s:
                s.discard(game)
            else:
                s.add(game)
            return game in s

    def owned_games(self, label):
        """Jeux possédés : ceux de la sélection (ordre du catalogue), puis les autres
        (catalogue complet)."""
        s = self.owned[label]
        return [g for g in GAMES_BY[label] if g in s] + \
            sorted(g for g in s if g not in SEL_SET[label])

    def count(self, label):
        """Jeux possédés de la sélection (pour la progression)."""
        s = self.owned[label]
        return sum(1 for g in GAMES_BY[label] if g in s)

    def condition(self, label, game):
        return self.conditions.get(key_of(label, game), DEFAULT_COND)

    def set_condition(self, label, game, cond):
        with self.lock:
            self.conditions[key_of(label, game)] = cond

    def manual_price(self, label, game):
        return self.manual.get(key_of(label, game))

    def set_manual(self, label, game, value):
        with self.lock:
            if value is None:
                self.manual.pop(key_of(label, game), None)
            else:
                self.manual[key_of(label, game)] = value

    def fixed_url(self, label, game):
        return self.urls.get(key_of(label, game))

    def set_fixed_url(self, label, game, url):
        with self.lock:
            if url:
                self.urls[key_of(label, game)] = url
            else:
                self.urls.pop(key_of(label, game), None)


# ====================================================================== réseau
class PriceError(Exception):
    pass


class Blocked(PriceError):
    pass


def is_challenge(status, text):
    """Page anti-robot de Cloudflare ? (on regarde le TITRE : les pages normales de
    PriceCharting contiennent aussi des scripts Cloudflare « challenge-platform »)."""
    t = text[:5000] if text else ""
    m = re.search(r"<title>(.*?)</title>", t, re.S | re.I)
    title = m.group(1) if m else ""
    return "Just a moment" in title or "Attention Required" in title or \
        (status in (403, 503) and "cloudflare" in t.lower())


TRANSIENT_RE = re.compile(r"anti-robot|bloqu|pause|connexion|délai|vérification|panne|"
                          r"navigateur|HTTP 5", re.I)


# Nettoyage des pages DANS le navigateur, avant de les passer à Python : scripts, styles,
# icônes, commentaires, en-tête, boutons « ajouter à ma collection », bulles d'aide et
# attributs inutiles. ≈ 60 % de données en moins (liste d'une console : 672 → 150 Ko),
# vérifié sans aucune différence de résultat sur 457 vraies pages.
SHRINK_RULES = [r"<script[\s\S]*?</script>", r"<style[\s\S]*?</style>",
                r"<svg[\s\S]*?</svg>", r"<!--[\s\S]*?-->",
                r"<(head|noscript|footer|nav)[\s\S]*?</\1>",
                r'<td class="add_to container">[\s\S]*?</td>',
                r'<div class="tour">[\s\S]*?</div>',
                r'\s(onclick|style|title|data-[a-z-]+)="[^"]*"']
SHRINK_JS = "".join("t = t.replace(/%s/gi, '');" % r.replace("/", "\\/") for r in SHRINK_RULES) + \
    "t = t.replace(/\\s+/g, ' ');"


def shrink_page(t):
    """Même nettoyage, côté Python (pour les tests et la connexion directe)."""
    for r in SHRINK_RULES:
        t = re.sub(r, "", t, flags=re.I)
    return re.sub(r"\s+", " ", t)


try:   # libère la mémoire des objets iOS créés depuis une tâche de fond (doc objc_util)
    from objc_util import autoreleasepool
except Exception:
    autoreleasepool = contextlib.nullcontext


class VerifySheet(ui.View):
    """Fenêtre affichée quand PriceCharting demande une vérification « humaine »."""

    def __init__(self, fetcher):
        super().__init__()
        self.fetcher = fetcher
        self.name = "Vérification PriceCharting"
        self.background_color = "white"
        self.msg = ui.Label()
        self.msg.text = ("PriceCharting vérifie que tu n'es pas un robot. Si une case "
                         "apparaît, touche-la, puis patiente : la fenêtre se fermera "
                         "toute seule et les prix reprendront.")
        self.msg.number_of_lines = 0
        self.msg.font = ("<System>", 14)
        self.msg.text_color = "#1c1c1e"
        self.add_subview(self.msg)
        self.later = ui.Button(title="Plus tard")
        self.later.font = ("<System-Bold>", 15)
        self.later.tint_color = "#007aff"
        self.later.action = lambda s: self.close()
        self.add_subview(self.later)

    def layout(self):
        w, h = self.width, self.height
        self.msg.frame = (14, 6, w - 28, 66)
        self.later.frame = (w - 120, h - 46, 110, 40)
        if self.fetcher.box.superview is self:
            self.fetcher.box.frame = (0, 76, w, max(0, h - 76 - 50))

    def will_close(self):
        self.fetcher.cancelled = True
        if self.fetcher.box.superview is self:
            self.remove_subview(self.fetcher.box)
        self.fetcher.sheet = None
        on_main(self.fetcher.attach_hidden)


class WebFetcher:
    """Navigateur intégré (moteur Safari) caché derrière l'app. Il exécute le JavaScript
    et garde les cookies : une vérification anti-robot validée une fois reste valable.
    Si la vérification demande une action, la page est montrée à l'utilisateur."""

    def __init__(self, host):
        self.host = host
        self.box = ui.View()
        self.box.background_color = "white"
        self.wv = ui.WebView()
        self.wv.scales_page_to_fit = False
        self.box.add_subview(self.wv)
        self.sheet = None
        self.cancelled = False
        self.ok_logged = False
        self.fast_logged = False
        self.attach_hidden()

    def attach_hidden(self):
        """Derrière les écrans de l'app : invisible mais actif."""
        w, h = 320, 480   # petit format : moins de mémoire
        parent = self.box.superview
        if parent is not None and parent is not self.host:
            try:
                parent.remove_subview(self.box)
            except Exception:
                pass
        if self.box.superview is None:
            self.host.add_subview(self.box)
        self.box.frame = (0, 0, w, h)
        self.wv.frame = (0, 0, w, h)
        self.box.touch_enabled = False
        try:
            self.box.send_to_back()   # derrière tous les écrans de l'app
        except Exception:
            log_exception("Impossible de cacher le navigateur intégré")
            self.box.alpha = 0.01

    def show_to_user(self):
        if self.sheet is not None:  # déjà affichée
            return
        log("Vérification PriceCharting affichée à l'utilisateur", "ALERTE")
        if self.box.superview is not None:
            self.box.superview.remove_subview(self.box)
        self.sheet = VerifySheet(self)
        self.sheet.add_subview(self.box)
        self.box.touch_enabled = True
        self.box.alpha = 1.0
        self.sheet.present("sheet")
        self.sheet.layout()
        self.wv.frame = (0, 0, self.box.width, self.box.height)

    def hide_from_user(self):
        sheet, self.sheet = self.sheet, None
        if sheet is not None:
            if self.box.superview is sheet:
                sheet.remove_subview(self.box)
            try:
                sheet.close()
            except Exception:
                pass
        self.attach_hidden()

    def open_manually(self):
        """Montre PriceCharting pour faire la vérification soi-même (bouton du Journal)."""
        self.wv.load_url(LIGHT_URL)
        self.show_to_user()
        self.sheet.later.title = "Fermer"

    def _js(self, code):
        try:
            return self.wv.eval_js(code) or ""
        except Exception:
            return ""

    def _read_js_text(self, var, total):
        """Lit une grande chaîne JavaScript par morceaux de 50 000 caractères
        (un seul très gros texte entre le navigateur et Python est risqué)."""
        parts = []
        for i in range(0, total, 50000):
            parts.append(self._js("%s.substr(%d, 50000)" % (var, i)))
        self._js("%s = null; ''" % var)
        return "".join(parts)

    def _page_html(self):
        n = self._js("window.__cj_html = document.documentElement.outerHTML; "
                     "String(window.__cj_html.length)")
        try:
            return self._read_js_text("window.__cj_html", int(n))
        except ValueError:
            return ""

    def _on_site(self):
        """Une page PriceCharting (vérification passée) est-elle ouverte ?"""
        return self._js("location.hostname") == "www.pricecharting.com" and \
            "Just a moment" not in self._js("document.title")

    def _fetch(self, url, data=None):
        """Mode rapide : télécharge la page depuis la page déjà ouverte (cookies de la
        vérification inclus) SANS l'afficher : ni images, ni pubs, ni scripts.
        Renvoie (url finale, html), ou None s'il faut repasser par l'affichage."""
        if data:   # formulaire « page suivante » (POST)
            options = "{credentials: 'include', method: 'POST', headers: {'Content-Type': " \
                      "'application/x-www-form-urlencoded'}, body: %s}" % json.dumps(urlencode(data))
        else:
            options = "{credentials: 'include'}"
        js_start = ("window.__cj_res = null; window.__cj_txt = null;"
                    "fetch(%s, %s).then(function (r) {"
                    "  return r.text().then(function (t) {"
                    "    var ch = /<title>[^<]*(Just a moment|Attention Required)/i.test(t);"
                    % (json.dumps(url), options))
        js_end = ("    window.__cj_txt = t;"
                  "    window.__cj_res = JSON.stringify({s: r.status, u: r.url, n: t.length, ch: ch});"
                  "  });"
                  "}).catch(function (e) { window.__cj_res = JSON.stringify({err: String(e)}); });"
                  "'ok'")
        started = self._js(js_start + SHRINK_JS + js_end)
        if started != "ok":
            return None
        deadline = time.time() + 25
        res = ""
        while time.time() < deadline and not res:
            time.sleep(0.3)
            res = self._js("window.__cj_res || ''")
        if not res:
            raise PriceError("délai dépassé (site trop lent ou pas de connexion)")
        try:
            info = json.loads(res)
        except ValueError:
            return None
        if "err" in info:
            raise PriceError("pas de connexion internet (%s)" % info["err"][:60])
        page = self._read_js_text("window.__cj_txt", int(info.get("n") or 0))
        status = int(info.get("s") or 0)
        if info.get("ch") or status in (403, 429, 503):
            log("Mode rapide : nouvelle vérification anti-robot demandée", "AVERT")
            return None                     # → affichage de la page (vérification)
        if status == 404:
            raise PriceError("page introuvable (404)")
        if status != 200:
            raise PriceError("erreur HTTP %d" % status)
        if not self.fast_logged:
            self.fast_logged = True
            log("Navigateur intégré : mode rapide actif (pages téléchargées sans affichage)")
        return info.get("u") or url, page

    def get(self, url, data=None):
        """Les pages sont toujours TÉLÉCHARGÉES (mode rapide). Le navigateur n'affiche
        que la page légère LIGHT_URL, pour passer la vérification anti-robot."""
        for attempt in range(2):
            if attempt or not self._on_site():
                self._navigate(LIGHT_URL)     # vérification si besoin (page légère)
            got = self._fetch(url, data)
            if got:
                return got
        raise Blocked("vérification anti-robot non passée")

    def _navigate(self, url):
        """Affiche la page dans le navigateur (nécessaire pour la vérification)."""
        self.cancelled = False
        self._js("window.__cj_old = 1;")  # repère : disparaît quand la nouvelle page est chargée
        on_main(self.wv.load_url, url)
        start = time.time()
        deadline = start + WEB_TIMEOUT
        shown = False
        try:
            while time.time() < deadline and not self.cancelled:
                time.sleep(0.7)
                ready = self._js("(typeof window.__cj_old === 'undefined' && "
                                 "document.readyState === 'complete') ? 'ok' : ''")
                if ready != "ok":
                    continue
                title = self._js("document.title")
                if "Just a moment" in title or "Un instant" in title:
                    # La vérification ne passe pas toute seule : on la montre.
                    if not shown and time.time() - start > 8:
                        shown = True
                        deadline = time.time() + 180
                        on_main(self.show_to_user)
                    continue
                time.sleep(0.3)
                page = self._page_html()
                href = self._js("location.href") or url
                if page:
                    if shown:
                        log("Vérification PriceCharting réussie")
                    if not self.ok_logged:
                        self.ok_logged = True
                        log("Navigateur intégré : première page chargée (%s)" % title[:50])
                    return href, page
        finally:
            if shown:
                on_main(self.hide_from_user)
        log("Navigateur intégré : échec (titre de la page : %r, adresse : %s)"
            % (self._js("document.title")[:60], self._js("location.href")[:90]), "AVERT")
        if self.cancelled:
            raise Blocked("vérification PriceCharting reportée (« Plus tard »)")
        raise Blocked("le navigateur intégré n'a pas pu charger la page (vérification "
                      "anti-robot non terminée ou pas de connexion)")


class Fetcher:
    """Une requête à la fois, avec un écart minimum entre deux requêtes.
    1) module requests (rapide) ; 2) si le site le bloque, navigateur intégré."""

    HEADERS = {
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
                      "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 "
                      "Mobile/15E148 Safari/604.1",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
    }

    def __init__(self):
        self.lock = threading.Lock()
        self.last_request = 0.0
        self.blocked_until = 0.0
        self.use_web = False
        self.web = None
        self.web_host = None   # fenêtre principale (le navigateur est créé à la demande)
        self._session = None

    def session(self):
        import requests
        if self._session is None:
            s = requests.Session()
            s.headers.update(self.HEADERS)
            self._session = s
        return self._session

    def blocked_minutes(self):
        left = self.blocked_until - time.time()
        return int(left / 60) + 1 if left > 0 else 0

    def mode_text(self):
        return "navigateur intégré" if self.use_web else "connexion directe"

    def ensure_web(self):
        """Crée le navigateur intégré seulement quand il sert (depuis un fil de fond :
        la création est faite par l'interface)."""
        if self.web is None and self.web_host is not None:
            done = threading.Event()

            def make():
                try:
                    self.make_web_now()
                finally:
                    done.set()
            on_main(make)
            done.wait(15)
        return self.web

    def make_web_now(self):
        """À appeler depuis l'interface."""
        if self.web is None and self.web_host is not None:
            try:
                self.web = WebFetcher(self.web_host)
                log("Navigateur intégré créé")
            except Exception:
                log_exception("Création du navigateur intégré impossible")
        return self.web

    def _pace(self):
        wait = self.last_request + MIN_GAP + random.uniform(0, 1.5) - time.time()
        if wait > 0:
            time.sleep(wait)
        self.last_request = time.time()

    def _requests_get(self, url, data=None):
        import requests
        last_error = None
        for attempt in range(2):
            if attempt:
                time.sleep(5)
            self._pace()
            try:
                if data:
                    r = self.session().post(url, data=data, timeout=20)
                else:
                    r = self.session().get(url, timeout=20)
            except requests.exceptions.Timeout:
                last_error = "délai dépassé (site trop lent)"
                continue
            except requests.exceptions.RequestException:
                last_error = "pas de connexion internet (ou site injoignable)"
                continue
            text = r.text or ""
            if is_challenge(r.status_code, text) or r.status_code in (403, 429):
                save_debug(text)
                raise Blocked("PriceCharting bloque les requêtes directes (code %d)"
                              % r.status_code)
            if r.status_code == 404:
                raise PriceError("page introuvable (404)")
            if r.status_code >= 500:
                last_error = "site en panne (code %d)" % r.status_code
                continue
            if r.status_code != 200:
                raise PriceError("erreur HTTP %d" % r.status_code)
            return r.url, text
        raise PriceError(last_error or "échec de la connexion")

    def get(self, url, params=None, data=None):
        """GET (ou POST si « data » est fourni : pages suivantes d'une liste)."""
        """Renvoie (url finale, html)."""
        if params:
            url = url + ("&" if "?" in url else "?") + urlencode(params)
        with self.lock:
            mins = self.blocked_minutes()
            if mins:
                raise Blocked("PriceCharting est en pause encore %d min" % mins)
            if self.use_web and self.ensure_web() is None:
                self.use_web = False
            if not self.use_web:
                try:
                    return self._requests_get(url, data)
                except Blocked:
                    if self.ensure_web() is None:
                        self.blocked_until = time.time() + BLOCK_PAUSE
                        log("Requêtes bloquées et pas de navigateur intégré : pause", "ALERTE")
                        raise
                    self.use_web = True  # bascule sur le navigateur intégré
                    log("Requêtes directes bloquées : passage au navigateur intégré", "ALERTE")
            self._pace()
            try:
                with autoreleasepool():
                    final, page = self.web.get(url, data)
            except Blocked as ex:
                self.blocked_until = time.time() + BLOCK_PAUSE
                log("Navigateur intégré bloqué (%s) : pause %d min" % (ex, BLOCK_PAUSE // 60),
                    "ALERTE")
                raise
            if is_challenge(200, page):
                self.blocked_until = time.time() + BLOCK_PAUSE
                log("Vérification anti-robot non passée : pause", "ALERTE")
                raise Blocked("vérification anti-robot non passée")
            return final, page

    def get_json(self, url, params):
        """Pour l'API officielle (clé) : requests uniquement."""
        import requests
        with self.lock:
            self._pace()
            try:
                r = self.session().get(url, params=params, timeout=20)
            except requests.exceptions.RequestException:
                raise PriceError("pas de connexion internet (ou site injoignable)")
            if r.status_code != 200:
                raise PriceError("API PriceCharting : erreur HTTP %d" % r.status_code)
            try:
                return r.json()
            except ValueError:
                raise PriceError("réponse de l'API illisible")


NET = Fetcher()


# ====================================================================== lecture des pages
AMOUNT = r"\$\s*([\d,]+(?:\.\d{1,2})?)"
LOT_WORDS = re.compile(r"\b(lot|lots|bundle|joblot|job lot|collection of|x\s?[2-9]|"
                       r"[2-9]\s?x|games|jeux|manual only|notice seule|case only|"
                       r"boitier seul|box only|cover only)\b", re.I)


def _amount(s):
    return float(s.replace(",", ""))


def search_url(label, game):
    q = "%s %s" % (search_name(game), PC[label][1])
    return BASE + "/search-products?type=prices&q=" + quote_plus(q)


COVER_RE = re.compile(r"https://storage\.googleapis\.com/images\.pricecharting\.com/"
                      r"[A-Za-z0-9_\-]+/(?:60|240|1600)\.jpg")


def cover_url(src):
    """Adresse de la jaquette en 240 px (bonne qualité, fichier léger)."""
    m = COVER_RE.search(src or "")
    return re.sub(r"/(?:60|1600)\.jpg$", "/240.jpg", m.group(0)) if m else None


def _clean_text(s):
    return re.sub(r"\s+", " ", htmllib.unescape(re.sub(r"<[^>]+>", " ", s))).strip()


def parse_search(page, slug):
    """Résultats de recherche de la console voulue : [{url, title, guide}]."""
    results = []
    chunks = re.split(r'<tr id="product-\d+"', page)[1:]
    for chunk in chunks:
        chunk = chunk.split("</tr>", 1)[0]
        m = re.search(r'<td class="title">\s*<a href="([^"]+)"[^>]*>(.*?)</a>', chunk, re.S)
        if not m:
            continue
        url = m.group(1)
        if url.startswith("/"):
            url = BASE + url
        if "/game/%s/" % slug not in url:
            continue
        guide = {}
        for cond, v in COND.items():
            p = re.search(r'<td class="price numeric %s">\s*<span class="js-price">\s*%s'
                          % (v[3], AMOUNT), chunk)
            guide[cond] = _amount(p.group(1)) if p else None
        im = re.search(r'<img class="photo"[^>]*src="([^"]+)"', chunk)
        results.append({"url": url.split("?")[0], "title": _clean_text(m.group(2)),
                        "guide": guide, "img": cover_url(im.group(1)) if im else None})
    return results


def parse_console_page(page, slug):
    """Page « liste d'une console » (150 jeux par page, du plus populaire au moins
    populaire) : ([{url, title, guide, img}], champs du formulaire « page suivante »)."""
    results = []
    for chunk in re.split(r'<tr id="product-\d+"', page)[1:]:
        chunk = chunk.split("</tr>", 1)[0]
        m = re.search(r'<td class="title"[^>]*>\s*<a href="([^"]+)"[^>]*>(.*?)</a>', chunk, re.S)
        if not m:
            continue
        url = m.group(1)
        if url.startswith("/"):
            url = BASE + url
        if "/game/%s/" % slug not in url:
            continue
        guide = {}
        for cond, v in COND.items():
            p = re.search(r'<td class="price numeric %s">\s*<span class="js-price">\s*%s'
                          % (v[3], AMOUNT), chunk)
            guide[cond] = _amount(p.group(1)) if p else None
        im = re.search(r'<img class="photo"[^>]*src="([^"]+)"', chunk)
        results.append({"url": htmllib.unescape(url.split("?")[0]),
                        "title": _clean_text(m.group(2)), "guide": guide,
                        "img": cover_url(im.group(1)) if im else None})
    form = re.search(r'<form[^>]*js-next-page[^>]*>(.*?)</form>', page, re.S)
    nxt = None
    if form:
        nxt = dict(re.findall(r'<input type="hidden" name="([^"]+)" value="([^"]*)"',
                              form.group(1)))
        if "cursor" not in nxt:
            nxt = None
    return results, nxt


def exact_key(name):
    return frozenset(title_tokens(name))


def fetch_console_list(label, form=None, us=False):
    """Une page de la liste d'une console (form=None : la 1re page)."""
    slug = US_PC[label][0] if us else PC[label][0]
    url = BASE + "/console/" + slug
    _, page = NET.get(url, data=form) if form else NET.get(url)
    return parse_console_page(page, slug)


def parse_game_page(page):
    """Page d'un jeu : nom, cotes, ventes eBay réalisées par condition, jaquette."""
    m = re.search(r'<h1 id="product_name"[^>]*>(.*?)<a', page, re.S)
    title = _clean_text(m.group(1)) if m else ""
    img = cover_url(page)

    guide = {}
    for cond, v in COND.items():
        m = re.search(r'<td[^>]*id="%s"[^>]*>(.*?)</td>' % v[0], page, re.S)
        p = re.search(AMOUNT, m.group(1)) if m else None
        guide[cond] = _amount(p.group(1)) if p else None

    sales = {}
    for cond, v in COND.items():
        start = page.find('<div class="completed-auctions-%s"' % v[1])
        values = []
        if start >= 0:
            end = page.find('<div class="completed-auctions-', start + 10)
            block = page[start:end if end > 0 else start + 200000]
            for row in re.split(r'<tr id="', block)[1:]:
                row = row.split("</tr>", 1)[0]
                p = re.search(r'class="js-price"\s*>\s*' + AMOUNT, row)
                if not p:
                    continue
                t = re.search(r'<td class="title">(.*?)</td>', row, re.S)
                if t and LOT_WORDS.search(_clean_text(t.group(1))):
                    continue  # lots, notices seules, boîtiers seuls...
                values.append(_amount(p.group(1)))
        g = guide.get(cond)
        if g and values:  # écarte les ventes aberrantes
            kept = [x for x in values if g / 3.0 <= x <= g * 3.0]
            values = kept or values
        sales[cond] = values
    return title, guide, sales, img


# ---------------------------------------------------------------- choix du bon jeu
ROMAN = {"i": "1", "ii": "2", "iii": "3", "iv": "4", "v": "5", "vi": "6", "vii": "7",
         "viii": "8", "ix": "9", "x": "10", "xi": "11", "xii": "12", "xiii": "13"}
STOP = {"the", "a", "an", "of", "and", "de", "la", "le", "les", "du", "des", "et"}
EDITION = {"platinum", "essentials", "classics", "greatest", "hits", "selects", "players",
           "player", "choice", "edition", "special", "limited", "collectors", "collector",
           "steelbook", "version", "budget", "best", "favourites", "favorites", "pal",
           "uk", "fr", "french", "german", "italian", "spanish", "value", "nintendo",
           "playstation", "ps2", "ps3", "ps4", "ps5", "wii", "xbox", "360", "ds", "3ds",
           "gamecube", "switch", "one", "series", "remastered", "hits", "playstation-hits",
           "n64", "game", "video", "standard", "reprint", "new", "big"}
BAD = {"demo", "promo", "manual", "guide", "strategy", "case", "only", "soundtrack",
       "amiibo", "controller", "bundle", "console", "system", "pack", "box", "art",
       "poster", "not", "resale", "disc", "cover", "sleeve", "kiosk", "trial", "press",
       "kit", "slim", "wheel", "force", "steering", "headset", "microphone", "mic",
       "dvd", "movie", "film", "figure", "statue", "book", "artbook", "cd", "vinyl",
       "card", "cards", "plush", "keychain", "memory", "adapter", "cable", "stand"}
MATCH_MIN = 0.6


def title_tokens(s):
    s = normalize(s).replace("&", " and ")
    s = re.sub(r"\btom clancy'?s?\b", " ", s)          # « Tom Clancy's Splinter Cell »
    s = re.sub(r"\b(the )?legend of zelda\b", "zelda", s)  # PriceCharting : « Zelda ... »
    s = re.sub(r"'s\b", "", s).replace("'", "").replace(".", "")
    s = re.sub(r"(?<=[a-z0-9])-(?=[a-z])", "", s)      # Spider-Man → spiderman
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return [ROMAN.get(t, t) for t in s.split() if t not in STOP]


def _merge(tokens, other):
    """Recolle deux mots si l'autre titre les écrit attachés (Soul Calibur / SoulCalibur)."""
    out, i = [], 0
    while i < len(tokens):
        if i + 1 < len(tokens) and tokens[i] + tokens[i + 1] in other:
            out.append(tokens[i] + tokens[i + 1])
            i += 2
        else:
            out.append(tokens[i])
            i += 1
    return out


def match_score(wanted, candidate):
    """1 = même titre ; diminue avec les mots en trop ou manquants."""
    wl, cl = title_tokens(wanted), title_tokens(candidate)
    wl = _merge(wl, set(cl))
    cl = _merge(cl, set(wl))
    w, c = set(wl), set(cl)
    common = len(w & c)
    if not common:
        return 0.0
    missing = w - c
    complete = not missing
    penalty = 0.0
    for t in c - w:
        if t in BAD:
            penalty += 2.0       # démo, promo, notice, pack console...
        elif t.isdigit():
            penalty += 2.0       # « Halo 3 » ≠ « Halo 3 ODST » ≠ « Halo 4 »
        elif t in EDITION:
            penalty += 0.15      # « Platinum » : même jeu, réédition
        else:
            penalty += 0.4 if complete and len(w) > 1 else 1.0
    penalty += sum(1.5 if t.isdigit() else 1.0 for t in missing)
    return common / (len(w) + penalty)


def name_variants(game):
    """(nom, coefficient) : titre complet, autres titres « X / Y », titres sans sous-titre."""
    names = [search_name(game)] + [strip_accents(p.strip().replace("’", "'"))
                                   for p in SEARCH_ALIASES.get(game, game).split(" / ")[1:]]
    out = [(n, 1.0) for n in names]
    for n in names:
        if ":" in n:
            out.append((n.split(":")[0].strip(), 0.95))
    return out


def best_match(game, results):
    names = name_variants(game)
    best, best_score = None, 0.0
    for r in results:
        score = max(match_score(n, r["title"]) * k for n, k in names)
        if score > best_score:
            best, best_score = r, score
    return (best, best_score) if best_score >= MATCH_MIN else (None, best_score)


# ---------------------------------------------------------------- récupération d'un prix
def _entry(url, title, guide, sales, partial, img=None, region="PAL"):
    return {"v": CACHE_VERSION, "ts": time.time(), "url": url, "title": title,
            "guide": guide, "sales": sales, "partial": partial, "img": img,
            "region": region}


def region_of(url):
    return "PAL" if "/game/pal-" in (url or "") else "US"


def fetch_game_page(url):
    final, page = NET.get(url)
    title, guide, sales, img = parse_game_page(page)
    if not any(guide.values()) and not any(sales.values()):
        save_debug(page)
        raise PriceError("page lue mais prix non reconnus (voir debug_pricecharting.html)")
    final = final.split("?")[0]
    return _entry(final, title, guide, sales, False, img, region_of(final))


def fetch_api(label, game, token):
    """API officielle PriceCharting (clé personnelle). Prix renvoyés en centimes USD."""
    _, pcname = PC[label]
    q = "%s %s" % (search_name(game), pcname)
    data = NET.get_json(BASE + "/api/products", {"t": token, "q": q})
    if data.get("status") != "success":
        raise PriceError("API PriceCharting : %s"
                         % data.get("error-message", "erreur (clé invalide ?)"))
    products = [p for p in (data.get("products") or [])
                if (p.get("console-name") or "").lower() == pcname.lower()]
    cands = [{"title": p.get("product-name") or "", "p": p} for p in products]
    best, _ = best_match(game, cands)
    if not best:
        raise PriceError("introuvable sur PriceCharting (%s)" % pcname)
    p = best["p"]

    def cents(field):
        v = p.get(field)
        if isinstance(v, (int, float)) and not isinstance(v, bool) and v > 0:
            return v / 100.0
        return None

    guide = {c: cents(v[2]) for c, v in COND.items()}
    if not any(guide.values()):
        raise PriceError("pas de cote pour ce jeu")
    return _entry(search_url(label, game), best["title"], guide, {}, True)


def _search_once(game, query, slug, console_name):
    """Une recherche. Renvoie ('page', entrée) / ('row', résultat) / None."""
    final, page = NET.get(BASE + "/search-products",
                          {"type": "prices", "q": "%s %s" % (query, console_name)})
    if "/game/%s/" % slug in final:  # le site a redirigé directement vers un jeu : on vérifie
        title, guide, sales, img = parse_game_page(page)
        score = max(match_score(n, title) * k for n, k in name_variants(game))
        if score >= MATCH_MIN and (any(guide.values()) or any(sales.values())):
            final = final.split("?")[0]
            return "page", _entry(final, title, guide, sales, False, img, region_of(final))
        return None
    best, _ = best_match(game, parse_search(page, slug))
    return ("row", best) if best else None


def find_product(label, game):
    """Cherche le jeu : 1) titre complet en PAL ; 2) titre court en PAL ;
    3) en dernier recours, la version US (jeu jamais sorti en Europe)."""
    slug, pcname = PC[label]
    full = search_name(game)
    queries = [full]
    short = full.split(":")[0].strip()
    if short != full and len(short) >= 3:
        queries.append(short)
    for q in queries:
        found = _search_once(game, q, slug, pcname)
        if found:
            return found
    us_slug, us_name = US_PC[label]
    return _search_once(game, full, us_slug, us_name)


def fetch_prices(label, game, fixed_url=None, known_url=None, full=False, token=None):
    """Prix d'un jeu.
    - fiche connue (corrigée à la main ou trouvée avant) : 1 requête sur la page du jeu ;
    - sinon : recherche (qui contient déjà les cotes de chaque résultat) ;
      full=True ajoute la page du jeu (ventes détaillées)."""
    if token and not fixed_url:
        return fetch_api(label, game, token)
    url = fixed_url or known_url
    if url:
        return fetch_game_page(url)
    found = find_product(label, game)
    if not found:
        raise PriceError("introuvable sur PriceCharting (%s). Utilise « Corriger la fiche » "
                         "pour choisir le bon jeu." % PC[label][1])
    kind, data = found
    if kind == "page":
        return data
    if full or not any(data["guide"].values()):
        return fetch_game_page(data["url"])
    return _entry(data["url"], data["title"], data["guide"], {}, True, data.get("img"),
                  region_of(data["url"]))


def estimate(entry, cond, fx):
    """Prix typique = cote PriceCharting (à défaut, médiane des ventes).
    Fourchette = quart le moins cher → quart le plus cher des ventes récentes."""
    if not isinstance(entry, dict) or not isinstance(entry.get("guide"), dict):
        return None
    guide = entry["guide"].get(cond)
    sales = sorted(x for x in ((entry.get("sales") or {}).get(cond) or [])
                   if isinstance(x, (int, float)))
    if guide:
        mid = guide
    elif sales:
        mid = quantile(sales, 0.5)
    else:
        return None
    if len(sales) >= 3:
        lo, hi = quantile(sales, 0.25), quantile(sales, 0.75)
        lo, hi = min(lo, mid), max(hi, mid)
    else:
        lo = hi = mid
    return {"min": lo * fx, "mid": mid * fx, "max": hi * fx, "n": len(sales),
            "manual": False}


# ====================================================================== cache des prix
class PriceCache:
    def __init__(self):
        self.lock = threading.RLock()
        raw = read_json(CACHE_FILE)
        self.data = raw if isinstance(raw, dict) else {}
        self.data.pop("_blocked_until", None)  # ancienne version : pause ignorée
        b = self.data.get("_pause_until")
        if isinstance(b, (int, float)) and b > time.time():
            NET.blocked_until = b  # la pause survit à la fermeture de l'app
        if self.data.get("_web_mode"):
            NET.use_web = True     # le site avait bloqué les requêtes directes

    def get(self, key):
        e = self.data.get(key)
        return e if isinstance(e, dict) else None

    def put(self, key, entry):
        with self.lock:
            self.data[key] = entry

    def forget(self, key):
        with self.lock:
            self.data.pop(key, None)

    def record_error(self, key, message):
        """Garde l'ancien prix s'il existe, note seulement l'erreur."""
        now = time.time()
        with self.lock:
            old = self.get(key)
            if self.has_price(old):
                new = dict(old)
                new.update({"err": message, "err_ts": now})
            else:
                new = {"v": CACHE_VERSION, "ts": now, "err": message, "err_ts": now}
                if old and old.get("url"):
                    new["url"] = old["url"]
            self.data[key] = new

    def save(self):
        with self.lock:
            self.data["_pause_until"] = NET.blocked_until
            self.data["_web_mode"] = NET.use_web
            try:
                write_json(CACHE_FILE, dict(self.data))
            except (OSError, TypeError, ValueError) as e:
                log("Sauvegarde du cache des prix impossible : %s" % e, "ERREUR")

    @staticmethod
    def has_price(e):
        return bool(e) and e.get("v") == CACHE_VERSION and isinstance(e.get("guide"), dict)

    def known_url(self, key):
        e = self.get(key)
        return e.get("url") if e and e.get("v") == CACHE_VERSION and \
            "/game/" in (e.get("url") or "") else None

    def is_fresh(self, key):
        e = self.get(key)
        return self.has_price(e) and time.time() - e.get("ts", 0) <= CACHE_TTL

    def needs_fetch(self, key):
        e = self.get(key)
        if not e or e.get("v") != CACHE_VERSION:
            return True
        now = time.time()
        err_ts = e.get("err_ts")
        if isinstance(err_ts, (int, float)):
            if e.get("poison"):
                # nouvelle version de l'app : on retente une fois (le correctif peut aider)
                wait = POISON_TTL if e.get("poison_v") == APP_VERSION else 0
            elif TRANSIENT_RE.search(e.get("err") or ""):
                wait = RETRY_SOON
            else:
                wait = ERR_TTL
            if now - err_ts < wait:
                return False
        if self.has_price(e):
            return now - e.get("ts", 0) > CACHE_TTL
        return True

    # -------------------------------------------------- taux de change
    def fx_quick(self):
        """Taux sans appel réseau (pour l'affichage dans la liste)."""
        c = self.data.get("_fx")
        if isinstance(c, dict) and isinstance(c.get("rate"), (int, float)):
            return float(c["rate"])
        return DEFAULT_FX

    def get_fx(self):
        c = self.data.get("_fx")
        valid = isinstance(c, dict) and isinstance(c.get("rate"), (int, float))
        if valid and time.time() - c.get("ts", 0) < 24 * 3600:
            return float(c["rate"]), "taux du jour"
        import requests
        sources = (
            ("https://api.frankfurter.dev/v1/latest?base=USD&symbols=EUR",
             lambda j: j["rates"]["EUR"]),
            ("https://api.frankfurter.app/latest?from=USD&to=EUR",
             lambda j: j["rates"]["EUR"]),
            ("https://open.er-api.com/v6/latest/USD", lambda j: j["rates"]["EUR"]),
        )
        for url, pick in sources:
            try:
                rate = float(pick(requests.get(url, timeout=10).json()))
                if 0.3 < rate < 3:
                    with self.lock:
                        self.data["_fx"] = {"rate": rate, "ts": time.time()}
                    self.save()
                    return rate, "taux du jour"
            except Exception:
                continue
        if valid:
            return float(c["rate"]), "ancien taux (hors ligne)"
        return DEFAULT_FX, "taux APPROXIMATIF %s (hors ligne)" % str(DEFAULT_FX).replace(".", ",")



# ====================================================================== rareté
# Basée sur la cote « Disque seul » en euros (à défaut, la cote « Complet »).
RARITY = [  # (seuil minimum en €, nom, nombre d'étoiles, couleur)
    (0, "Commun", 1, "#8e8e93"),
    (10, "Peu commun", 2, "#34c759"),
    (25, "Rare", 3, "#0a84ff"),
    (50, "Très rare", 4, "#af52de"),
    (100, "Légendaire", 5, "#ff9f0a"),
]
SORTS = ["N°", "Prix", "Rareté", "A–Z"]
FILTERS = ["Tous", "Obtenus", "Manquants"]


def rarity_for(value_eur):
    if value_eur is None:
        return None
    tier = RARITY[0]
    for t in RARITY:
        if value_eur >= t[0]:
            tier = t
    return tier


def stars(n):
    return "★" * n + "☆" * (5 - n)


# ====================================================================== thème
def ui_style():
    try:
        return "dark" if ui.get_ui_style() == "dark" else "light"
    except Exception:
        return "light"


THEMES = {
    "dark": {"bg": "#000000", "card": "#1c1c1e", "field": "#2c2c2e", "text": "#f2f2f7",
             "sub": "#98989f", "line": "#38383a", "owned": "#32d74b", "accent": "#0a84ff",
             "status": "#ff9f0a", "header": "#1c1c1e", "placeholder": "#2c2c2e",
             "indicator": "white", "style": "dark"},
    "light": {"bg": "#f2f2f7", "card": "#ffffff", "field": "#e5e5ea", "text": "#1c1c1e",
              "sub": "#6e6e73", "line": "#d1d1d6", "owned": "#248a3d", "accent": "#007aff",
              "status": "#c76a00", "header": "#ffffff", "placeholder": "#e5e5ea",
              "indicator": "black", "style": "light"},
}


def make_theme(style=None):
    """Couleurs de l'app selon le mode clair/sombre de l'iPhone (ui.get_ui_style)."""
    return dict(THEMES[style or ui_style()])


def _rgba_key(color):
    """Couleur -> clé comparable (Pythonista rend les couleurs en tuples RGBA)."""
    try:
        c = ui.parse_color(color) if isinstance(color, str) else tuple(color)
        return tuple(int(round(x * 255)) for x in c[:4])
    except Exception:
        return None


# Couleurs du thème utilisées comme FOND et comme TEXTE. Séparées pour qu'un texte blanc
# (bouton bleu, numéro « #001 »...) ne soit jamais pris pour le fond blanc d'une carte.
BG_KEYS = ("bg", "card", "field", "line", "header", "placeholder", "owned", "accent")
TEXT_KEYS = ("text", "sub", "owned", "accent", "status", "line")
ATTR_KEYS = {"background_color": BG_KEYS, "border_color": BG_KEYS + TEXT_KEYS,
             "text_color": TEXT_KEYS, "tint_color": TEXT_KEYS}


def theme_mappings(old, new):
    out = {}
    for attr, keys in ATTR_KEYS.items():
        m = {}
        for k in keys:
            key = _rgba_key(old[k])
            if key is not None:
                m.setdefault(key, new[k])
        out[attr] = m
    return out


def recolor(view, mappings, indicator):
    """Remplace dans toutes les vues les couleurs de l'ancien thème par celles du nouveau.
    Les couleurs qui ne dépendent pas du thème (rareté, bandeaux, blanc) ne bougent pas."""
    for attr, mapping in mappings.items():
        try:
            value = getattr(view, attr)
        except Exception:
            continue
        key = _rgba_key(value) if value is not None else None
        if key in mapping:
            try:
                setattr(view, attr, mapping[key])
            except Exception:
                pass
    if isinstance(view, ui.ScrollView):
        view.indicator_style = indicator
    for sub in list(getattr(view, "subviews", []) or []):
        recolor(sub, mappings, indicator)


# ====================================================================== jaquettes
class CoverStore:
    """Télécharge les jaquettes une fois, les garde dans Documents/jaquettes,
    et prépare une version grise pour les jeux pas encore obtenus."""

    def __init__(self, app):
        self.app = app
        self.lock = threading.Lock()
        self.queue = []          # jaquettes à télécharger, la première d'abord
        self.urgent = []         # fiche ouverte : avant tout le reste
        self.failed = set()
        self.event = threading.Event()
        try:
            os.makedirs(COVER_DIR, exist_ok=True)
        except OSError:
            pass
        colors = read_json(os.path.join(COVER_DIR, "couleurs.json"))
        self.colors = colors if isinstance(colors, dict) else {}   # url -> couleur moyenne
        self.colors_dirty = 0

    def save_colors(self):
        if self.colors_dirty:
            self.colors_dirty = 0
            try:
                write_json(os.path.join(COVER_DIR, "couleurs.json"), dict(self.colors))
            except OSError:
                pass

    def color(self, url, grey=False):
        """Couleur moyenne de la jaquette (affichée en attendant l'image)."""
        c = self.colors.get(url) if url else None
        if not c or not grey:
            return c
        r, g, b = int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16)
        y = int(0.3 * r + 0.59 * g + 0.11 * b)
        return "#%02x%02x%02x" % (y, y, y)

    def set_window(self, urls):
        """Jaquettes à l'écran puis juste à côté, dans l'ordre : SEULES celles-ci sont
        téléchargées (celles qui sont sorties de l'écran sont retirées de la file)."""
        with self.lock:
            self.queue = [u for u in urls
                          if u and u not in self.failed and not self.has(u)]
        if self.queue:
            self.event.set()

    _paths = {}
    _files = None

    @classmethod
    def path(cls, url, grey=False):
        k = (url, grey)
        p = cls._paths.get(k)
        if p is None:
            h = hashlib.md5(url.encode("utf-8")).hexdigest()
            p = cls._paths[k] = os.path.join(COVER_DIR, h + ("_g" if grey else "") + ".jpg")
        return p

    @classmethod
    def has_file(cls, p):
        """Fichier présent ? (liste du dossier lue une fois, puis tenue à jour en mémoire :
        plus d'accès disque à chaque défilement)."""
        if cls._files is None:
            try:
                cls._files = set(os.path.join(COVER_DIR, f) for f in os.listdir(COVER_DIR))
            except OSError:
                cls._files = set()
        return p in cls._files

    def has(self, url, grey=False):
        return bool(url) and self.has_file(self.path(url, grey))

    def local(self, url, grey=False):
        """Chemin du fichier s'il existe déjà, sinon None (et demande le téléchargement)."""
        if not url:
            return None
        p = self.path(url, grey)
        if self.has_file(p):
            return p
        if grey and self.has(url):
            return None  # couleur dispo mais pas de gris (pas de PIL) : l'appelant atténue
        self.want(url)
        return None

    def want(self, url):
        """Jaquette demandée en priorité (fiche ouverte)."""
        with self.lock:
            if url in self.failed or self.has(url):
                return
            if url in self.urgent:
                self.urgent.remove(url)
            self.urgent.append(url)
        self.event.set()

    def worker(self):
        import requests
        while not self.app.closed:
            if self.app.in_background():          # rien à afficher : on attend
                time.sleep(2)
                continue
            with self.lock:
                if self.urgent:
                    url = self.urgent.pop()
                elif self.queue:
                    url = self.queue.pop(0)          # à l'écran d'abord, puis à côté
                else:
                    url = None
            if url and self.has(url):
                continue
            if not url:
                self.save_colors()
                self.event.wait(20)
                self.event.clear()
                continue
            try:
                r = requests.get(url, timeout=15, headers={"User-Agent": Fetcher.HEADERS["User-Agent"]})
                if r.status_code != 200 or not r.content:
                    raise IOError("HTTP %d" % r.status_code)
                tmp = self.path(url) + ".tmp"
                with open(tmp, "wb") as f:
                    f.write(r.content)
                color = self._make_grey(tmp, self.path(url, True))
                os.replace(tmp, self.path(url))
                CoverStore.has_file(self.path(url))
                CoverStore._files.add(self.path(url))
                if os.path.exists(self.path(url, True)):
                    CoverStore._files.add(self.path(url, True))
                if color:
                    self.colors[url] = color
                    self.colors_dirty += 1
                    if self.colors_dirty >= 20:
                        self.save_colors()
            except Exception as ex:
                with self.lock:
                    self.failed.add(url)
                log("Jaquette non téléchargée (%s) : %s" % (ex, url[-40:]), "AVERT")
                try:
                    os.remove(self.path(url) + ".tmp")
                except OSError:
                    pass
                continue
            self.app.notify_cover(url)
            time.sleep(0.15)

    @staticmethod
    def _make_grey(src, dst):
        """Version grise (jeux manquants) + couleur moyenne. Renvoie la couleur."""
        try:
            from PIL import Image, ImageEnhance
            im = Image.open(src).convert("RGB")
            r, g, b = im.resize((1, 1)).getpixel((0, 0))
            grey = ImageEnhance.Brightness(im.convert("L")).enhance(0.9).convert("RGB")
            grey.save(dst + ".tmp", "JPEG", quality=80)
            os.replace(dst + ".tmp", dst)   # jamais d'image à moitié écrite à l'écran
            return "#%02x%02x%02x" % (r, g, b)
        except Exception:
            return None


IMAGE_CACHE = collections.OrderedDict()   # chemin -> ui.Image (les plus récentes)
IMAGE_CACHE_MAX = 48   # ≈ l'écran + la zone juste avant/après (le reste est déchargé)


def load_image(path):
    """Jaquette en mémoire, avec un cache limité aux 60 dernières.
    (ui.Image.named garderait TOUTES les jaquettes en mémoire jusqu'à la fermeture :
    ~70 Mo pour tout le catalogue, de quoi pousser iOS à fermer l'app.)"""
    if not path:
        return None
    img = IMAGE_CACHE.pop(path, None)
    if img is None:
        try:
            with open(path, "rb") as f:
                img = ui.Image.from_data(f.read())
        except Exception:
            return None
        if img is None:
            return None
    IMAGE_CACHE[path] = img            # en dernier = le plus récent
    while len(IMAGE_CACHE) > IMAGE_CACHE_MAX:
        IMAGE_CACHE.popitem(last=False)
    return img


# ====================================================================== photos des consoles
def console_icon_url(label):
    name = RA_ICONS.get(label)
    return RA_ICON_BASE + quote(name) + ".png" if name else None


def pick_console_photo(rows):
    """Photo de la console : la ligne « ... Console / System » la plus simple
    (sans manette, sans édition limitée si possible)."""
    best = None
    for r in rows:
        t = r["title"]
        if not r.get("img") or not re.search(r"\b(console|system)\b", t, re.I):
            continue
        if re.search(r"controller|manette|pad\b|adapter|cable|memory", t, re.I):
            continue
        score = (("[" in t) + ("bundle" in t.lower()) + ("edition" in t.lower()), len(t))
        if best is None or score < best[0]:
            best = (score, r["img"])
    return best[1] if best else None


# ====================================================================== catalogue complet
NON_GAME = {"console", "system", "controller", "memory", "adapter", "cable", "headset",
            "strategy", "guide", "manual", "kiosk", "camera", "remote", "charger", "steering",
            "wheel", "microphone", "keyboard", "mouse", "faceplate", "battery", "dock",
            "stylus", "sensor", "amiibo", "figure", "statue", "soundtrack", "artbook",
            "poster", "skin", "case", "sleeve", "stand", "headphones", "vr", "move"}
VARIANT_SKIP = re.compile(r"\[[^\]]*(demo|promo|resale|press|kiosk|disc only|manual|bundle|"
                          r"console|starter|pack)[^\]]*\]|\bslim\b|\bstarter pack\b|"
                          r"\bmetallic\b|^\s*playstation \d (?!all)|\s\+\s", re.I)


# Mentions d'édition / réédition qui ne changent pas le jeu (supprimées pour comparer).
# Précis : « Ultimate Spider-Man », « Tomb Raider Anniversary » ou « Pokémon Gold » restent
# des jeux distincts ; seules les mentions d'ÉDITION (« ... Edition », [Platinum]...) partent.
_EDITION_RE = re.compile(
    r"\[[^\]]*\]|\([^)]*\)"
    r"|\b(?:platinum|essentials|greatest hits|playstation hits|player'?s? choice|"
    r"nintendo selects|xbox classics|game of the year|goty|director'?s cut|not for resale|"
    r"steelbook)\b"
    r"|\b(?:collector'?s|limited|special|deluxe|gold|complete|definitive|ultimate|premium|"
    r"day one|launch|anniversary|standard|legacy|bonus disc|signature|exclusive|"
    r"steelbook|champions?|platinum|enhanced)\s+(?:edition|version|pack)\b"
    r"|\b(?:edition|version)\b", re.I)
_CANON = {}
_SQUASH = {}


def base_key(title):
    """Clé anti-doublon : mots normalisés (accents, &/and, II/2, tirets, « The »...)
    sans les mentions d'édition, dans n'importe quel ordre. Gardée en mémoire."""
    k = _CANON.get(title)
    if k is None:
        k = _CANON[title] = frozenset(title_tokens(_EDITION_RE.sub(" ", normalize(title))))
    return k


def squash_key(title):
    """2e clé : lettres et chiffres collés (« Ghosthunter » = « Ghost Hunter »)."""
    k = _SQUASH.get(title)
    if k is None:
        k = _SQUASH[title] = "".join(sorted(base_key(title))) and \
            re.sub(r"[^a-z0-9]", "", " ".join(title_tokens(_EDITION_RE.sub(" ", normalize(title)))))
    return k


def _plainness(title):
    """Plus c'est petit, plus le titre est « l'édition normale » (à préférer)."""
    return (len(_EDITION_RE.findall(normalize(title))), len(title))


class FullCatalog:
    """Tous les jeux d'une console, lus sur les listes PriceCharting (150 par page),
    sans accessoires ni doublons d'édition. Gardé dans Documents/catalogue_complet/."""

    def __init__(self):
        self.data = {}
        self.sel_keys = {}

    def path(self, label):
        return os.path.join(FULL_DIR, "%s.json" % label)

    def get(self, label):
        d = self.data.get(label)
        if d is None:
            raw = read_json(self.path(label))
            d = raw if isinstance(raw, dict) and isinstance(raw.get("rows"), list) else \
                {"rows": [], "form": None, "done": False, "ts": 0}
            self.data[label] = d
            self.compact(label)
        return d

    def compact(self, label, extra_titles=()):
        """Retire les doublons (y compris ceux d'une ancienne version du filtre) et les
        jeux déjà dans la sélection. Une seule passe, par dictionnaire."""
        d = self.get(label)
        sel = self.selection_keys(label) | set(base_key(t) for t in extra_titles)
        sel_sq = self.selection_squash(label) | set(squash_key(t) for t in extra_titles)
        keep, bases, squashes = [], {}, {}
        for r in d["rows"]:
            k, q = base_key(r[0]), squash_key(r[0])
            if not k or k in sel or q in sel_sq:
                continue
            i = bases.get(k)
            if i is None:
                i = squashes.get(q)
            if i is None:
                bases[k] = squashes[q] = len(keep)
                keep.append(r)
            else:
                bases.setdefault(k, i)
                squashes.setdefault(q, i)
                if _plainness(r[0]) < _plainness(keep[i][0]):
                    keep[i] = r               # on garde l'édition normale
        d["rows"], d["bases"], d["squash"] = keep, bases, squashes
        d["by"] = {r[0]: i for i, r in enumerate(keep)}

    def names(self, label):
        return [r[0] for r in self.get(label)["rows"]]

    def row(self, label, game):
        if game in SEL_SET[label]:
            return None
        d = self.get(label)
        i = d["by"].get(game)
        return d["rows"][i] if i is not None else None

    def index(self, label, game):
        return self.get(label)["by"].get(game)

    def done(self, label):
        d = self.get(label)
        return d.get("done") and time.time() - d.get("ts", 0) < CACHE_TTL

    def selection_keys(self, label):
        if label not in self.sel_keys:
            keys = set()
            for g in GAMES_BY[label]:
                for n in self.selection_names(g):
                    keys.add(base_key(n))
            keys.discard(frozenset())
            self.sel_keys[label] = keys
        return self.sel_keys[label]

    @staticmethod
    def selection_names(g):
        """Tous les noms sous lesquels un jeu de la sélection peut apparaître."""
        out = []
        variants = name_variants(g)
        for n, k in variants:
            # titre court (sans sous-titre) seulement s'il a un numéro : « Metal Gear
            # Solid 2 » = « Metal Gear Solid 2: Sons of Liberty »
            if k == 1.0 or re.search(r"\d", n):
                out.append(n)
        parts = [p.strip() for p in SEARCH_ALIASES.get(g, g).split(" / ")]
        if len(parts) > 1:                    # « Pokémon Sword / Shield » -> « Pokémon Shield »
            first = parts[0].split()
            for p in parts[1:]:
                w = p.split()
                if len(w) < len(first):
                    out.append(" ".join(first[:len(first) - len(w)] + w))
        return out

    def selection_squash(self, label):
        k = "sq:" + label
        if k not in self.sel_keys:
            self.sel_keys[k] = set(squash_key(n) for g in GAMES_BY[label]
                                   for n in self.selection_names(g)) - {""}
        return self.sel_keys[k]

    def add_page(self, label, rows, form, first):
        d = self.get(label)
        if first:                             # 1re page (ou mise à jour mensuelle)
            d["rows"], d["by"], d["bases"], d["pages"] = [], {}, {}, 0
        d["pages"] = d.get("pages", 0) + 1
        n0 = len(d["rows"])
        for r in rows:
            title = r["title"]
            if VARIANT_SKIP.search(title) or (set(title_tokens(title)) & NON_GAME):
                continue
            if not base_key(title):
                continue
            d["rows"].append([title, r["url"], r["guide"].get("Disque seul"),
                              r["guide"].get("Complet"), r["guide"].get("Neuf"), r["img"]])
        self.compact(label)                   # dédoublonnage (2 clés, une passe)
        added = max(0, len(d["rows"]) - n0)
        d["form"] = form
        d["done"] = form is None
        d["ts"] = time.time()
        self.save(label)
        return added

    def save(self, label):
        d = self.get(label)
        try:
            os.makedirs(FULL_DIR, exist_ok=True)
            write_json(self.path(label), {k: d.get(k) for k in ("rows", "form", "done", "ts",
                                                                "pages")})
        except OSError as e:
            log("Catalogue complet %s non enregistré : %s" % (label, e), "ERREUR")

    def entry(self, label, game):
        r = self.row(label, game)
        if not r:
            return None
        e = _entry(r[1], r[0], {"Disque seul": r[2], "Complet": r[3], "Neuf": r[4]}, {}, True,
                   r[5], "PAL")
        e["ts"] = self.get(label).get("ts", 0)
        return e


# ====================================================================== cerveau de l'app
class App:
    """Données + chargement automatique des prix/jaquettes. Les vues s'y abonnent."""

    def __init__(self):
        self.theme = make_theme()
        self.coll = Collection()
        self.prices = PriceCache()
        self.covers = CoverStore(self)
        self.listeners = []
        self.closed = False
        self.wake = threading.Event()
        self.focus = None        # console affichée (ses jeux passent en priorité)
        self.priority = None     # (console, jeu) dont la fiche est ouverte
        self.loading = None
        self.status = ""
        self.busy = False
        self.fx_checked = False
        self.interrupted = False  # la session précédente s'est-elle mal fermée ?
        self.error_counts = {}
        self.update = None        # (version, code) si une mise à jour est disponible
        self.heartbeat = 0.0      # dernier passage de l'interface (détecteur de gel)
        self.user_busy_until = 0.0  # défilement en cours : le chargement patiente
        self.first_beat = 0.0     # premier passage de l'interface
        self.last_prices_save = time.time()
        self.added_dirty = False  # prix d'ajout figés à enregistrer
        self.bg_paused = False    # chargement en pause car l'app est en arrière-plan
        self.awake = False        # écran maintenu allumé pendant un gros chargement
        self.safe_mode = False    # démarrage sans chargement (après plantages répétés)
        self.loading_started = False
        self.events_lock = threading.Lock()
        self.dirty_games = set()
        self.dirty_covers = set()
        self.status_dirty = False
        self.number = {l: {g: i + 1 for i, g in enumerate(GAMES_BY[l])} for l in LABELS}
        self.full = FullCatalog()
        self.full_wanted = set()   # consoles dont le catalogue complet est demandé
        self.section_of = {l: {} for l in LABELS}
        for l in LABELS:
            for s, games in SECTIONS_BY[l]:
                for g in games:
                    self.section_of[l].setdefault(g, s)

    def start(self):
        run_named("veille", self.freeze_watchdog)
        run_named("demarrage", self.staged_start)

    def staged_start(self):
        """Démarre les tâches de fond une par une, seulement quand l'interface tourne
        normalement depuis quelques secondes (évite la surcharge au lancement)."""
        while not self.closed and not (self.first_beat and time.time() - self.first_beat > 4):
            time.sleep(0.5)
        if self.closed:
            return
        if self.safe_mode:
            log("MODE SANS ÉCHEC : prix et jaquettes en pause (plantages au démarrage)",
                "ALERTE")
        else:
            self.start_loading()
        time.sleep(6)
        if not self.closed:
            run_named("maj", self.update_worker)

    def start_loading(self):
        if self.loading_started:
            return
        self.loading_started = True
        run_named("prix", self.price_worker)
        run_named("jaquettes", self.covers.worker)

    def leave_safe_mode(self):
        log("Action : sortie du mode sans échec")
        self.safe_mode = False
        self.start_loading()
        self.notify()

    def matched_titles(self, label):
        """Titres PriceCharting trouvés pour les jeux de la sélection : leurs variantes
        n'apparaissent pas une 2e fois dans le catalogue complet."""
        out = []
        for g in GAMES_BY[label]:
            e = self.prices.get(key_of(label, g))
            if e and e.get("title"):
                out.append(e["title"])
        return out

    def full_step(self, label):
        """Une page du catalogue complet (150 jeux)."""
        d = self.full.get(label)
        form = d.get("form") if not d.get("done") else None
        first = form is None
        page_no = 1 if first else d.get("pages", 0) + 1
        self.set_status("Catalogue complet %s : %d jeux, page %d..." % (label, len(d["rows"]),
                                                                       page_no))
        try:
            rows, nxt = fetch_console_list(label, form)
        except Exception as ex:
            log("Catalogue complet %s : %s" % (label, ex), "AVERT")
            time.sleep(10)
            return
        added = self.full.add_page(label, rows, nxt, first)
        self.full.compact(label, self.matched_titles(label))
        if nxt is None:
            log("Catalogue complet %s : %d jeux" % (label, len(d["rows"])))
            self.set_status("Catalogue complet %s : %d jeux" % (label, len(d["rows"])))
        elif page_no >= 80:
            d["done"] = True
            self.full.save(label)
        if added or nxt is None:
            self.notify(label, None)

    def _run_bulk(self, label):
        try:
            with open(JOB_FILE, "w", encoding="utf-8") as f:
                f.write("%s|__liste__" % label)
        except OSError:
            pass
        try:
            self.bulk_console(label)
        except Exception as ex:
            log("Chargement rapide %s impossible (%s) : recherche jeu par jeu" % (label, ex),
                "AVERT")
            with self.prices.lock:   # on n'insiste pas : la recherche habituelle prend le relais
                self.prices.data.setdefault("_bulk", {})[label] = time.time()
        finally:
            try:
                os.remove(JOB_FILE)
            except OSError:
                pass

    def save_prices_soon(self):
        """Le fichier des prix (~300 Ko) est réécrit au plus toutes les 30 s pendant le
        chargement (au lieu d'après chaque jeu) : moins de batterie et d'usure.
        Il est aussi enregistré à la fermeture de l'app."""
        if time.time() - self.last_prices_save >= 30:
            self.last_prices_save = time.time()
            self.prices.save()

    def set_poison(self, key):
        """Le jeu en cours de chargement a fait planter l'app : on le met de côté."""
        if "|" not in key:
            return
        if key.endswith("|__liste__"):   # la liste rapide a fait planter : on s'en passe
            with self.prices.lock:
                self.prices.data.setdefault("_bulk", {})[key.split("|")[0]] = time.time()
            self.prices.save()
            log("Chargement rapide abandonné pour %s (plantage)" % key.split("|")[0], "ALERTE")
            return
        self.prices.record_error(key, "a fait planter l'app pendant son chargement : mis de "
                                      "côté 7 jours (« Corriger la fiche » ou « Saisir mon "
                                      "prix » possibles)")
        e = self.prices.get(key)
        if e:
            e["poison"] = True
            e["poison_v"] = APP_VERSION
        self.prices.save()
        log("Jeu mis de côté car il a fait planter l'app : %s" % key, "ALERTE")

    def freeze_watchdog(self):
        """Si l'interface ne répond plus (gel), note ce que fait chaque fil AVANT
        qu'iOS ne tue l'app : un gel laisse ainsi une trace dans le journal."""
        reported = False
        started = time.time()
        stable = False
        while not self.closed:
            time.sleep(2)
            if self.closed:
                break
            beats = getattr(self, "_beats", 0) + 1
            self._beats = beats
            if beats % 5 == 1:               # toutes les 10 s : « l'app est toujours en vie »
                write_marker(started)
            if not stable and time.time() - started > 60:
                stable = True                # 1 min sans plantage : compteur remis à 0
                try:
                    write_json(STARTS_FILE, {"early": 0})
                except OSError:
                    pass
            if not self.heartbeat:
                continue
            frozen = time.time() - self.heartbeat
            if frozen > 6 and not reported:
                reported = True
                stacks = []
                names = {t.ident: t.name for t in threading.enumerate()}
                for ident, frame in sys._current_frames().items():
                    stacks.append("--- fil %s ---\n%s" % (
                        names.get(ident, ident), "".join(traceback.format_stack(frame)[-8:])))
                log("Interface bloquée depuis %d s. État des fils :\n%s"
                    % (frozen, "\n".join(stacks)), "GEL")
            elif frozen < 2 and reported:
                log("Interface débloquée", "GEL")
                reported = False

    def update_worker(self):
        try:
            self.update = check_update()
        except Exception as ex:
            log("Vérification de mise à jour impossible : %s" % ex, "AVERT")
            return
        if self.update:
            log("Mise à jour disponible : %s" % self.update[0])
            self.notify()

    def retry_now(self):
        """Lève la pause : la vérification PriceCharting sera proposée à nouveau."""
        NET.blocked_until = 0
        self.prices.save()
        self.wake.set()
        self.set_status("Nouvel essai...")

    def stop(self):
        log("Fermeture normale de l'app")
        if self.awake:
            self.awake = False
            try:
                console.set_idle_timer_disabled(False)   # veille normale rétablie
            except Exception:
                pass
        try:
            os.remove(RUN_MARKER)
        except OSError:
            pass
        self.closed = True
        self.wake.set()
        self.covers.event.set()
        self.covers.save_colors()
        self.prices.save()
        if self.added_dirty:
            self.coll.save()

    # ---------------------------------------------------------- abonnements
    def subscribe(self, view):
        if view not in self.listeners:
            self.listeners.append(view)

    def unsubscribe(self, view):
        if view in self.listeners:
            self.listeners.remove(view)

    # Les fils de fond ne font que noter les changements ; flush_events() (fil de
    # l'interface) les transmet aux écrans, regroupés.
    def notify(self, label=None, game=None):
        with self.events_lock:
            self.dirty_games.add((label, game))

    def notify_cover(self, url):
        with self.events_lock:
            self.dirty_covers.add(url)

    def set_status(self, text):
        with self.events_lock:
            self.status = text
            self.status_dirty = True

    def flush_events(self):
        with self.events_lock:
            games, self.dirty_games = self.dirty_games, set()
            covers, self.dirty_covers = self.dirty_covers, set()
            status_dirty, self.status_dirty = self.status_dirty, False
        if not (games or covers or status_dirty):
            return
        if len(games) > 12 or (None, None) in games:
            games = {(None, None)}           # beaucoup de changements : tout redessiner
        if len(covers) > 12:
            covers, games = set(), games | {(None, None)}
        for v in list(self.listeners):
            if status_dirty:
                guard(v.on_status)(self.status)
            for label, game in games:
                guard(v.on_data)(label, game)
            for url in covers:
                guard(v.on_cover)(url)

    # ---------------------------------------------------------- lecture des données
    def entry(self, label, game):
        e = self.prices.get(key_of(label, game))
        if PriceCache.has_price(e):
            return e
        return self.full.entry(label, game)

    def cover_url(self, label, game):
        e = self.prices.get(key_of(label, game))
        if e and e.get("v") == CACHE_VERSION and e.get("img"):
            return e["img"]
        r = self.full.row(label, game)
        return r[5] if r else None

    def console_photo(self, label):
        rec = (self.prices.data.get("_console_img") or {}).get(label)
        return rec.get("url") if isinstance(rec, dict) else None

    def set_console_photo(self, label, url):
        with self.prices.lock:
            self.prices.data.setdefault("_console_img", {})[label] = {"url": url,
                                                                      "ts": time.time()}
        if url:
            self.covers.want(url)

    def photo_needed(self, label):
        rec = (self.prices.data.get("_console_img") or {}).get(label)
        if not isinstance(rec, dict):
            return True
        return not rec.get("url") and time.time() - rec.get("ts", 0) > 7 * 24 * 3600

    def photo_step(self, label):
        """Photo d'une console (1re page de sa liste PriceCharting)."""
        self.set_status("Photo de la console %s..." % FULL_NAME[label])
        try:
            rows, _ = fetch_console_list(label)
        except Exception as ex:
            log("Photo de la console %s : %s" % (label, ex), "AVERT")
            rows = []
        url = pick_console_photo(rows)
        if not url:                          # pas de photo en PAL : version US
            try:
                url = pick_console_photo(fetch_console_list(label, us=True)[0])
            except Exception:
                url = None
        self.set_console_photo(label, url)
        self.save_prices_soon()
        self.notify()

    def num(self, label, game):
        n = self.number[label].get(game)
        if n is None:
            i = self.full.index(label, game)
            n = len(GAMES_BY[label]) + 1 + i if i is not None else 0
        return n

    def section(self, label, game):
        return self.section_of[label].get(game) or "Catalogue complet"

    def price(self, label, game, cond=None):
        """{'mid','min','max','n','manual'} en euros, ou None."""
        manual = self.coll.manual_price(label, game)
        if manual is not None:
            return {"min": manual, "mid": manual, "max": manual, "n": 0, "manual": True}
        e = self.entry(label, game)
        if not e:
            return None
        return estimate(e, cond or self.coll.condition(label, game), self.prices.fx_quick())

    def delta(self, label, game):
        """(prix à l'ajout, écart actuel) en €, ou None. Si le prix n'était pas connu à
        l'ajout, il est figé dès qu'il le devient."""
        if not self.coll.is_owned(label, game):
            return None
        p = self.price(label, game)
        if not p:
            return None
        key = key_of(label, game)
        rec = self.coll.added.get(key)
        if not rec or rec.get("p") is None:
            with self.coll.lock:
                rec = self.coll.added.setdefault(key, {"ts": time.time()})
                rec["p"] = round(p["mid"], 2)
            self.added_dirty = True
            return rec["p"], 0.0
        return rec["p"], round(p["mid"] - rec["p"], 2)

    def rarity(self, label, game):
        e = self.entry(label, game)
        if not e:
            return None
        fx = self.prices.fx_quick()
        for c in ("Disque seul", "Complet"):
            g = e["guide"].get(c)
            if g:
                return rarity_for(g * fx)
        return None

    def error_of(self, label, game):
        e = self.prices.get(key_of(label, game))
        if e and e.get("v") == CACHE_VERSION and e.get("err") and not self.entry(label, game):
            return e["err"]
        return None

    def console_value(self, label):
        total, known = 0.0, 0
        for g in self.coll.owned_games(label):
            p = self.price(label, g)
            if p:
                total += p["mid"]
                known += 1
        return total, known

    # ---------------------------------------------------------- actions
    def toggle(self, label, game):
        now = self.coll.toggle(label, game)
        key = key_of(label, game)
        with self.coll.lock:
            if now:   # prix figé à la date d'ajout
                p = self.price(label, game)
                self.coll.added[key] = {"ts": time.time(), "p": round(p["mid"], 2) if p else None}
            else:
                self.coll.added.pop(key, None)
        log("Action : %s %s | %s" % ("ajout de" if now else "retrait de", label, game))
        self.save()
        self.notify(label, game)
        return now

    def save(self):
        err = self.coll.save()
        if err:
            hud("Erreur de sauvegarde : %s" % err, "error", 2.5)

    def refetch(self, label, game, full=False):
        self.prices.forget(key_of(label, game))
        if full:
            self.priority = (label, game)
        self.notify(label, game)
        self.wake.set()

    # ---------------------------------------------------------- chargement automatique
    def _needs(self, label, game, full=False):
        key = key_of(label, game)
        if not full and not self.prices.get(key) and self.full.row(label, game):
            return False   # prix déjà donné par la liste du catalogue complet
        if full:
            e = self.prices.get(key)
            if self.prices.is_fresh(key) and not e.get("partial"):
                return False
            err_ts = (e or {}).get("err_ts")
            return not (isinstance(err_ts, (int, float)) and time.time() - err_ts < 120)
        return self.prices.needs_fetch(key)

    def next_job(self):
        """(console, jeu, type) : fiche ouverte, puis jeux possédés, puis chargement
        rapide des listes de console, puis console affichée, puis le reste du catalogue."""
        if self.priority and self._needs(self.priority[0], self.priority[1], True):
            return self.priority + (True,)
        for l in LABELS:
            for g in self.coll.owned_games(l):
                if self._needs(l, g):
                    return l, g, False
        for l in ([self.focus] if self.focus in self.full_wanted else []) + \
                sorted(self.full_wanted):
            if not self.full.done(l):
                return l, None, "complet"
        for l in ([self.focus] if self.focus else []) + LABELS:
            if self.bulk_needed(l):
                return l, None, "liste"
        order = []
        if self.focus:
            order.append([(self.focus, g) for g in GAMES_BY[self.focus]])
        order.append([(l, g) for l in LABELS for g in GAMES_BY[l]])
        for group in order:
            for l, g in group:
                if self._needs(l, g):
                    return l, g, False
        return None

    def bulk_needed(self, label):
        done = (self.prices.data.get("_bulk") or {}).get(label)
        if isinstance(done, (int, float)) and time.time() - done < CACHE_TTL:
            return False
        return any(self._needs(label, g) for g in GAMES_BY[label])

    def bulk_console(self, label):
        """Chargement rapide : lit les pages « liste de la console » et remplit d'un coup
        prix + jaquettes des jeux au titre IDENTIQUE. Les autres seront cherchés un par
        un (recherche habituelle, plus sûre pour les titres approchants)."""
        wanted = {}
        for g in GAMES_BY[label]:
            if self._needs(label, g) and not self.coll.fixed_url(label, g):
                for name, k in name_variants(g):
                    if k == 1.0:
                        wanted.setdefault(exact_key(name), g)
        found, form, page_no = 0, None, 0
        while wanted and page_no < BULK_PAGES and not self.closed:
            page_no += 1
            self.set_status("Chargement rapide %s : page %d/%d (%d jeux trouvés)"
                            % (label, page_no, BULK_PAGES, found))
            rows, form = fetch_console_list(label, form)
            if page_no == 1 and self.photo_needed(label):
                self.set_console_photo(label, pick_console_photo(rows))
            for row in rows:
                g = wanted.get(exact_key(row["title"]))
                if g is None or not any(row["guide"].values()):
                    continue
                self.prices.put(key_of(label, g), _entry(
                    row["url"], row["title"], row["guide"], {}, True, row["img"], "PAL"))
                for kk in [kk for kk, gg in wanted.items() if gg == g]:
                    del wanted[kk]
                found += 1
            self.notify()
            if not form:
                break
        with self.prices.lock:
            self.prices.data.setdefault("_bulk", {})[label] = time.time()
        log("Chargement rapide %s : %d jeux en %d page(s)" % (label, found, page_no))
        self.save_prices_soon()

    def remaining(self):
        return sum(1 for l in LABELS for g in GAMES_BY[l] if self.prices.needs_fetch(key_of(l, g)))

    def price_worker(self):
        time.sleep(0.8)
        while not self.closed:
            try:
                with autoreleasepool():     # libère les objets iOS à chaque étape
                    self._price_step()
            except Exception:
                log_exception("Erreur dans le chargement des prix")
                time.sleep(5)

    def log_price_error(self, label, game, ex):
        """Journalise un échec de prix sans inonder le journal (ex. : hors ligne)."""
        kind = re.sub(r"\d+", "#", str(ex))[:80]
        n = self.error_counts.get(kind, 0) + 1
        self.error_counts[kind] = n
        if n <= 3:
            log("Prix non trouvé %s | %s : %s" % (label, game, ex), "AVERT")
        elif n == 4:
            log("Même erreur sur d'autres jeux (suivantes masquées) : %s" % ex, "AVERT")

    def in_background(self):
        """L'app est-elle en arrière-plan (autre app ouverte, écran verrouillé) ?"""
        try:
            return console.is_in_background()
        except Exception:
            return False

    def pause_if_background(self):
        """En arrière-plan, iOS met le navigateur intégré en pause : on n'insiste pas
        (sinon délais dépassés, fausses erreurs, et risque qu'iOS ferme l'app)."""
        if not self.in_background():
            if self.bg_paused:
                self.bg_paused = False
                log("App revenue au premier plan : chargement repris")
            return False
        if not self.bg_paused:
            self.bg_paused = True
            log("App en arrière-plan : chargement en pause")
        time.sleep(3)
        return True

    def keep_awake(self, flag):
        """Pendant un gros chargement, l'écran ne se met pas en veille (sinon iOS
        suspend l'app et le chargement s'arrête). Rétabli dès que c'est fini."""
        if flag != self.awake:
            self.awake = flag
            on_main(console.set_idle_timer_disabled, flag)

    def _price_step(self):
        """Une étape : un jeu chargé (ou une attente)."""
        while time.time() < self.user_busy_until and not self.closed:
            time.sleep(0.15)                 # défilement en cours : fluidité d'abord
        if self.pause_if_background():
            return
        if NET.blocked_minutes():
            self.set_status("PriceCharting en pause encore %d min" % NET.blocked_minutes())
            self.wake.wait(60)
            self.wake.clear()
            return
        job = self.next_job()
        self.keep_awake(bool(job) and self.remaining() >= 20)
        if not job:
            self.loading = None
            self.set_status("Catalogue à jour : prix et jaquettes chargés")
            self.wake.wait(60)
            self.wake.clear()
            return
        if not self.fx_checked:
            self.prices.get_fx()
            self.fx_checked = True
        label, game, full = job
        if full == "liste":
            self._run_bulk(label)
            return
        if full == "complet":
            self.full_step(label)
            return
        if full == "photo":
            self.photo_step(label)
            return
        key = key_of(label, game)
        self.loading = (label, game)
        try:
            with open(JOB_FILE, "w", encoding="utf-8") as f:
                f.write(key)                 # si l'app plante maintenant, on saura sur quoi
        except OSError:
            pass
        left = self.remaining()
        self.set_status("Chargement %s : %s  (encore %d)" % (label, game, left))
        try:
            e = fetch_prices(label, game, fixed_url=self.coll.fixed_url(label, game),
                             known_url=self.prices.known_url(key) or (
                                 (self.full.row(label, game) or [None, None])[1]), full=full,
                             token=None if full else read_token())
            old = self.prices.get(key)
            if not e.get("img") and old and old.get("img"):
                e["img"] = old["img"]
            self.prices.put(key, e)
        except Exception as ex:
            self.prices.record_error(key, str(ex))
            self.log_price_error(label, game, ex)
        if full and self.priority == (label, game):
            self.priority = None
        self.loading = None
        try:
            os.remove(JOB_FILE)
        except OSError:
            pass
        self.save_prices_soon()
        if self.added_dirty:
            self.added_dirty = False
            self.save()
        self.notify(label, game)   # la jaquette sera téléchargée quand elle s'affichera


# ====================================================================== petits éléments
def make_label(text, frame, size=13, bold=False, color=None, align="left", lines=1):
    l = ui.Label(frame=frame)
    l.text = text
    l.font = ("<System-Bold>" if bold else "<System>", size)
    if color:
        l.text_color = color
    l.alignment = {"left": ui.ALIGN_LEFT, "center": ui.ALIGN_CENTER,
                   "right": ui.ALIGN_RIGHT}[align]
    l.number_of_lines = lines
    return l


def make_button(title, frame, action, color, text_color="white", size=14):
    """Bouton. Dans Pythonista, un bouton prend la taille de son titre : la taille
    voulue est donc appliquée EN DERNIER (sinon bouton rétréci et titre coupé)."""
    b = ui.Button()
    b.title = title
    b.font = ("<System-Bold>", size)
    b.background_color = color
    b.tint_color = text_color
    b.corner_radius = 10
    b.action = action
    b.frame = frame
    return b


UP, DOWN = "#34c759", "#ff3b30"


def delta_text(d, short=False):
    """(« ▲ +1,05 € » vert / « ▼ -1,05 € » rouge / « = »), couleur."""
    if not d:
        return "", "#8e8e93"
    diff = d[1]
    if abs(diff) < 0.01:
        return ("=" if short else "= prix inchangé"), "#8e8e93"
    s = eur(abs(diff)).replace(" €", "€") if short else eur(abs(diff))
    return ("▲ +" + s, UP) if diff > 0 else ("▼ -" + s, DOWN)


def make_pill(text, frame, size, bg, color="white", radius=None):
    """Étiquette sur fond arrondi. Le fond est porté par une vue (l'arrondi du fond
    d'un simple texte n'est pas appliqué dans Pythonista). Renvoie (cadre, texte)."""
    box = ui.View(frame=frame)
    box.background_color = bg
    box.corner_radius = frame[3] / 2.0 if radius is None else radius
    lbl = make_label(text, (0, 0, frame[2], frame[3]), size, True, color, "center")
    box.add_subview(lbl)
    return box, lbl


def native_style(view, style):
    """Force le style iOS (clair/sombre) des éléments natifs : onglets, champs de
    texte, barres de défilement... (Pythonista les dessine sinon en style clair)."""
    try:
        view.objc_instance.setOverrideUserInterfaceStyle_(2 if style == "dark" else 1)
    except Exception:
        pass


@guard_class
class Screen(ui.View):
    """Écran poussé dans la pile de navigation."""
    screen_title = ""

    def on_data(self, label, game):
        pass

    def on_cover(self, url):
        pass

    def on_status(self, text):
        pass

    def on_show(self):
        pass

    def on_hide(self):
        pass

    def later(self, fn, delay):
        """Regroupe les mises à jour rapprochées : fn n'est appelée qu'une fois,
        au bout de « delay » secondes (déclenchée par AppView.update)."""
        if getattr(self, "_later", None):
            return
        self._later = (time.time() + delay, fn)

    def run_due(self):
        due = getattr(self, "_later", None)
        if due and time.time() >= due[0]:
            self._later = None
            if not self.hidden:
                due[1]()


# ====================================================================== navigation
@guard_class
class AppView(ui.View):
    """Fenêtre principale : barre du haut (retour + titre) et pile d'écrans."""

    def __init__(self, app):
        super().__init__()
        self.app = app
        t = app.theme
        self.name = "Ma collection de jeux"
        self.background_color = t["bg"]
        self.stack = []
        self.update_interval = 0.25  # relève la boîte aux lettres (voir on_main)
        self.bar = ui.View(background_color=t["header"])
        self.add_subview(self.bar)
        self.back = ui.Button(title="‹ Retour")
        self.back.font = ("<System>", 16)
        self.back.tint_color = t["accent"]
        self.back.action = lambda s: self.pop()
        self.bar.add_subview(self.back)
        self.title_label = make_label("", (0, 0, 10, 10), 16, True, t["text"], "center")
        self.bar.add_subview(self.title_label)
        self.right = None
        self.line = ui.View(background_color=t["line"])
        self.bar.add_subview(self.line)
        native_style(self, t["style"])
        NET.web_host = self   # le navigateur intégré sera créé seulement s'il sert

    def push(self, screen):
        log("Écran : %s" % (screen.screen_title or type(screen).__name__))
        if self.stack:
            self.stack[-1].on_hide()
            self.stack[-1].hidden = True
        self.stack.append(screen)
        self.add_subview(screen)
        self.app.subscribe(screen)
        self.layout()
        screen.on_show()
        self._update_bar()

    def pop(self):
        if len(self.stack) <= 1:
            return
        s = self.stack.pop()
        s.on_hide()
        self.app.unsubscribe(s)
        self.remove_subview(s)
        top = self.stack[-1]
        top.hidden = False
        top.on_show()
        self.layout()
        self._update_bar()

    def _update_bar(self):
        top = self.stack[-1]
        self.title_label.text = top.screen_title
        self.back.hidden = len(self.stack) <= 1
        if self.right:
            self.bar.remove_subview(self.right)
            self.right = None
        item = getattr(top, "bar_button", None)
        if item:
            title, action = item
            b = ui.Button(title=title)
            b.font = ("<System>", 16)
            b.tint_color = self.app.theme["accent"]
            b.action = action
            self.right = b
            self.bar.add_subview(b)
        self.layout()

    def layout(self):
        w, h = self.width, self.height
        self.bar.frame = (0, 0, w, 44)
        self.back.frame = (4, 0, 90, 44)
        self.title_label.frame = (96, 0, w - 192, 44)
        if self.right:
            self.right.frame = (w - 100, 0, 96, 44)
        self.line.frame = (0, 43.5, w, 0.5)
        for s in self.stack:
            s.frame = (0, 44, w, h - 44)

    def update(self):
        """Appelée par Pythonista 4 fois par seconde, sur le fil de l'interface."""
        self.app.heartbeat = time.time()
        if not self.app.first_beat:
            self.app.first_beat = self.app.heartbeat
        self.ticks = getattr(self, "ticks", 0) + 1
        if self.ticks % 8 == 0 and ui_style() != self.app.theme["style"]:
            self.switch_theme(ui_style())   # l'iPhone est passé en mode nuit (ou jour)
        drain_main_queue()
        self.app.flush_events()
        for s in list(self.stack):
            s.run_due()
        if self.stack and hasattr(self.stack[-1], "idle"):
            self.stack[-1].idle()

    def switch_theme(self, style):
        """Change de thème en direct, sans relancer l'app."""
        old = dict(self.app.theme)
        new = make_theme(style)
        self.app.theme.clear()
        self.app.theme.update(new)        # les vues créées ensuite prennent le nouveau thème
        recolor(self, theme_mappings(old, new), new["indicator"])
        native_style(self, style)
        for s in list(self.stack):
            if hasattr(s, "on_theme"):
                s.on_theme()
        log("Thème %s appliqué en direct" % ("sombre" if style == "dark" else "clair"))

    def will_close(self):
        self.update_interval = 0
        self.app.stop()


# ====================================================================== accueil
@guard_class
class HomeScreen(Screen):
    screen_title = "Ma collection"

    def __init__(self, app, nav):
        super().__init__()
        self.app, self.nav = app, nav
        self.background_color = app.theme["bg"]
        self.bar_button = ("Exporter", lambda s: self.export())
        self.scroll = ui.ScrollView()
        self.scroll.indicator_style = app.theme["indicator"]
        self.scroll.always_bounce_vertical = True
        self.add_subview(self.scroll)
        self.status = make_label("", (0, 0, 10, 10), 11, False, app.theme["status"])
        self.add_subview(self.status)
        self.built_sig = None      # état des bandeaux + largeur au dernier dessin complet
        self.summary_refs = None   # étiquettes mises à jour sur place
        self.card_refs = {}

    def on_show(self):
        self.app.focus = None
        self.refresh_values()

    def on_data(self, label, game):
        if not self.hidden:
            self.later(self.refresh_values, 0.8)

    def on_cover(self, url):
        for label in list(getattr(self, "photo_refs", {})):
            if console_icon_url(label) == url:
                self.show_photo(label)

    def show_photo(self, label):
        """Icône RetroArch de la console si elle est téléchargée, sinon son sigle."""
        iv, ph = self.photo_refs.get(label, (None, None))
        if iv is None:
            return
        url = console_icon_url(label)
        path = self.app.covers.path(url) if url else None
        img = load_image(path) if path and CoverStore.has_file(path) else None
        if url and not img:
            self.app.covers.want(url)
        iv.image = img
        iv.hidden = img is None
        ph.hidden = img is not None

    def layout_sig(self):
        return (self.width, self.app.safe_mode, bool(self.app.update),
                bool(NET.blocked_minutes()), self.app.interrupted)

    def refresh_values(self):
        """Met à jour les chiffres sans recréer l'écran (moins de calcul). Redessine
        tout seulement si un bandeau apparaît/disparaît ou si la largeur change."""
        if self.built_sig != self.layout_sig() or not self.summary_refs:
            self.build()
            return
        count_lbl, value_lbl = self.summary_refs
        owned = sum(self.app.coll.count(l) for l in LABELS)
        total = sum(len(GAMES_BY[l]) for l in LABELS)
        value = sum(self.app.console_value(l)[0] for l in LABELS)
        count_lbl.text = "%d / %d jeux" % (owned, total)
        value_lbl.text = "Valeur estimée : %s" % eur(value)
        t = self.app.theme
        for label in list(getattr(self, "photo_refs", {})):
            iv, _ = self.photo_refs[label]
            if iv.hidden:
                self.show_photo(label)
        for label, (cnt, fill, sub, track_w) in self.card_refs.items():
            got, pct, text = self.card_texts(label)
            cnt.text = "%d / %d" % (got, len(GAMES_BY[label]))
            cnt.text_color = t["owned"] if got else t["sub"]
            fill.frame = (0, 0, max(6, track_w * pct), 6)
            fill.hidden = not got
            sub.text = text

    def card_texts(self, label):
        got, total = self.app.coll.count(label), len(GAMES_BY[label])
        value, known = self.app.console_value(label)
        pct = got / float(total) if total else 0
        text = "%d %%" % round(pct * 100)
        if got:
            text += "  •  %s" % eur_short(value)
        return got, pct, text

    def on_status(self, text):
        self.status.text = text

    def layout(self):
        w, h = self.width, self.height
        self.status.frame = (14, h - 22, w - 28, 18)
        self.scroll.frame = (0, 0, w, h - 24)
        self.build()

    def build(self):
        t = self.app.theme
        sv = self.scroll
        for v in list(sv.subviews):
            sv.remove_subview(v)
        w = self.width
        if w < 50:
            return
        pad = 14
        y = pad
        # --- résumé
        owned = sum(self.app.coll.count(l) for l in LABELS)
        total = sum(len(GAMES_BY[l]) for l in LABELS)
        value = sum(self.app.console_value(l)[0] for l in LABELS)
        if self.app.safe_mode:
            sv.add_subview(make_button("Mode sans échec (plantages au démarrage). Copie le "
                                       "rapport du Journal, puis touche ici pour reprendre",
                                       (pad, y, w - 2 * pad, 52),
                                       lambda s: (self.app.leave_safe_mode(), self.build()),
                                       "#ff3b30", "white", 13))
            y += 52 + pad
        if self.app.update:
            sv.add_subview(make_button("⬇︎ Mise à jour %s disponible – installer" %
                                       self.app.update[0].split(" ")[0],
                                       (pad, y, w - 2 * pad, 40), lambda s: self.do_update(),
                                       t["accent"], "white", 13))
            y += 40 + pad
        if NET.blocked_minutes():
            sv.add_subview(make_button("Prix en pause (vérification PriceCharting) – réessayer",
                                       (pad, y, w - 2 * pad, 40),
                                       lambda s: (self.app.retry_now(), self.build()),
                                       "#ff9f0a", "white", 13))
            y += 40 + pad
        if self.app.interrupted:
            warn = make_button("⚠︎ La dernière session s'est mal fermée – voir le journal",
                               (pad, y, w - 2 * pad, 40), lambda s: self.open_journal(),
                               "#ff9f0a", "white", 13)
            sv.add_subview(warn)
            y += 40 + pad
        card = ui.View(frame=(pad, y, w - 2 * pad, 172), background_color=t["card"])
        card.corner_radius = 14
        card.add_subview(make_label("Toutes consoles", (16, 12, w, 18), 13, False, t["sub"]))
        count_lbl = make_label("%d / %d jeux" % (owned, total), (16, 32, w, 30), 26, True,
                               t["text"])
        value_lbl = make_label("Valeur estimée : %s" % eur(value), (16, 64, w, 20), 15, False,
                               t["text"])
        card.add_subview(count_lbl)
        card.add_subview(value_lbl)
        self.summary_refs = (count_lbl, value_lbl)
        self.card_refs = {}
        cw = w - 2 * pad
        card.add_subview(make_button("Rapport de valeur", (16, 92, (cw - 44) / 2, 30),
                                     lambda s: self.app_value(None), t["accent"], size=13))
        card.add_subview(make_button("Rafraîchir les prix", (28 + (cw - 44) / 2, 92,
                                                              (cw - 44) / 2, 30),
                                     lambda s: self.refresh_all(), t["field"], t["accent"], 13))
        card.add_subview(make_button("Journal / signaler un problème", (16, 130, cw - 32, 30),
                                     lambda s: self.open_journal(), t["field"], t["sub"], 13))
        sv.add_subview(card)
        y += 172 + pad
        # --- sélecteur façon RetroArch : une rangée horizontale par famille, avec la
        # photo de chaque console
        cw, ch, gap = 148, 214, 12
        self.photo_refs = {}
        for family, labels in FAMILIES:
            color = FAMILY_COLORS.get(family, t["accent"])
            dot = ui.View(frame=(pad + 2, y + 5, 8, 8), background_color=color)
            dot.corner_radius = 4
            sv.add_subview(dot)
            got = sum(self.app.coll.count(l) for l in labels)
            sv.add_subview(make_label("%s   %d jeux" % (family.upper(), got) if got else
                                      family.upper(), (pad + 16, y, w, 18), 13, True, t["sub"]))
            y += 26
            row = ui.ScrollView(frame=(0, y, w, ch + 8))
            row.shows_horizontal_scroll_indicator = False
            row.always_bounce_horizontal = True
            row.indicator_style = t["indicator"]
            for i, label in enumerate(labels):
                row.add_subview(self.console_card(label, FULL_NAME[label],
                                                  (pad + i * (cw + gap), 2, cw, ch), color))
            row.content_size = (pad * 2 + len(labels) * (cw + gap) - gap, ch + 8)
            sv.add_subview(row)
            y += ch + 26
        sv.add_subview(make_label(RA_CREDIT, (pad, y, w - 2 * pad, 30), 10, False, t["sub"],
                                  "center", 2))
        y += 40
        sv.content_size = (w, y)
        self.built_sig = self.layout_sig()

    def console_card(self, label, full, frame, color):
        """Carte d'une console : photo, nom, progression (sélecteur façon RetroArch)."""
        t = self.app.theme
        x, y, w, h = frame
        card = ui.View(frame=frame, background_color=t["card"])
        card.corner_radius = 16
        stripe = ui.View(frame=(18, 0, w - 36, 4), background_color=color)
        stripe.corner_radius = 2
        card.add_subview(stripe)
        box = ui.View(frame=(8, 12, w - 16, 112), background_color=t["field"])
        box.corner_radius = 12
        ph = make_label(label, (0, 30, w - 16, 52), 28, True, color, "center")
        box.add_subview(ph)
        iv = ui.ImageView(frame=(10, 8, w - 36, 96))
        iv.content_mode = ui.CONTENT_SCALE_ASPECT_FIT
        box.add_subview(iv)
        card.add_subview(box)
        self.photo_refs[label] = (iv, ph)
        self.show_photo(label)
        got, pct, text = self.card_texts(label)
        card.add_subview(make_label(full, (8, 130, w - 16, 20), 14, True, t["text"], "center"))
        cnt = make_label("%d / %d" % (got, len(GAMES_BY[label])), (8, 152, w - 16, 18), 13,
                         True, t["owned"] if got else t["sub"], "center")
        card.add_subview(cnt)
        track = ui.View(frame=(16, 176, w - 32, 6), background_color=t["field"])
        track.corner_radius = 3
        fill = ui.View(frame=(0, 0, max(6, (w - 32) * pct), 6), background_color=color)
        fill.corner_radius = 3
        fill.hidden = not got
        track.add_subview(fill)
        card.add_subview(track)
        sub = make_label(text, (8, 188, w - 16, 16), 11, False, t["sub"], "center")
        card.add_subview(sub)
        self.card_refs[label] = (cnt, fill, sub, w - 32)
        b = ui.Button(frame=(0, 0, w, h))
        b.action = lambda s, l=label: self.nav.push(ConsoleScreen(self.app, self.nav, l))
        card.add_subview(b)
        return card

    @background
    def do_update(self):
        version, code = self.app.update
        log("Action : installation de la mise à jour %s" % version)
        try:
            console.alert("Mise à jour %s" % version,
                          "Installer la nouvelle version ? Ta collection est conservée.",
                          "Installer")
        except KeyboardInterrupt:
            return
        if apply_update(version, code):
            self.app.update = None
            on_main(self.build)

    def open_journal(self):
        self.app.interrupted = False
        self.nav.push(JournalScreen(self.app, self.nav))

    def refresh_all(self):
        n = 0
        for l in LABELS:
            for g in GAMES_BY[l]:
                e = self.app.prices.get(key_of(l, g))
                if e and e.get("v") == CACHE_VERSION:
                    e = dict(e)
                    e["ts"] = 0          # périmé : sera rechargé
                    e.pop("err_ts", None)
                    self.app.prices.put(key_of(l, g), e)
                    n += 1
        self.app.wake.set()
        hud("Mise à jour des prix lancée", "success", 1.0)

    def app_value(self, only):
        compute_value(self.app, only)

    @background
    def export(self):
        lines = []
        for label, full, sections, _, _ in CONSOLES:
            owned = self.app.coll.owned[label]
            lines += ["MA COLLECTION %s (%d/%d)" % (full.upper(), self.app.coll.count(label),
                                                   len(GAMES_BY[label])), ""]
            for section, games in sections:
                lines.append(section)
                for g in games:
                    lines.append("%s %s" % ("[x]" if g in owned else "[ ]", g))
                lines.append("")
            extra = [g for g in sorted(owned) if g not in SEL_SET[label]]
            if extra:
                lines.append("Autres jeux possédés")
                lines += ["[x] %s" % g for g in extra] + [""]
            lines.append("")
        try:
            import clipboard
            clipboard.set("\n".join(lines))
            alert("Liste copiée", "La checklist de toutes les consoles est dans le presse-papiers.")
        except Exception:
            alert("Copie impossible", "La sauvegarde est dans Documents/collection_jeux.json.")


# ====================================================================== grille d'une console
@guard_class
class ConsoleScreen(Screen):
    def __init__(self, app, nav, label):
        super().__init__()
        self.app, self.nav, self.label = app, nav, label
        t = app.theme
        self.screen_title = FULL_NAME[label]
        self.background_color = t["bg"]
        self.filter_index = 0
        self.sort_index = 0
        self.quick = False          # mode « toucher = cocher »
        self.query = ""
        self.items = []             # [("h", texte) | ("g", jeu)]
        self.frames = []
        self.live = {}              # index -> vue affichée
        self.pool = []              # cases recyclables (sorties de l'écran)
        self.tops, self.prefetch = [], []
        self.layout_width = 0
        self.bar_button = ("Trier : N°", lambda s: self.cycle_sort())

        self.search = ui.TextField()
        self.search.placeholder = "Rechercher dans %s..." % FULL_NAME[label]
        self.search.clear_button_mode = "while_editing"
        self.search.autocorrection_type = False
        self.search.spellchecking_type = False
        self.search.background_color = t["field"]
        self.search.text_color = t["text"]
        self.search.border_width = 0
        self.search.bordered = False     # sinon fond blanc par-dessus nos couleurs
        self.search.corner_radius = 9
        self.search.delegate = self
        self.add_subview(self.search)

        self.filter_ctrl = ui.SegmentedControl()
        self.filter_ctrl.segments = FILTERS
        self.filter_ctrl.selected_index = 0
        self.filter_ctrl.action = self.filter_changed
        self.add_subview(self.filter_ctrl)

        self.complete = False
        self.scope_ctrl = ui.SegmentedControl()
        self.scope_ctrl.segments = ["Sélection", "Catalogue complet"]
        self.scope_ctrl.selected_index = 0
        self.scope_ctrl.action = self.scope_changed
        self.add_subview(self.scope_ctrl)

        self.quick_ctrl = ui.SegmentedControl()
        self.quick_ctrl.segments = ["Toucher : voir la fiche", "Toucher : cocher"]
        self.quick_ctrl.selected_index = 0
        self.quick_ctrl.action = self.quick_changed
        self.add_subview(self.quick_ctrl)

        self.summary = make_label("", (0, 0, 10, 10), 13, True, t["text"])
        self.add_subview(self.summary)
        self.status = make_label("", (0, 0, 10, 10), 11, False, t["status"])
        self.add_subview(self.status)

        self.scroll = ui.ScrollView()
        self.scroll.indicator_style = app.theme["indicator"]
        self.scroll.delegate = self
        self.scroll.always_bounce_vertical = True
        self.add_subview(self.scroll)

    # ---------------------------------------------------------- cycle de vie
    def on_show(self):
        self.app.focus = self.label
        self.app.wake.set()
        self.status.text = self.app.status
        self.rebuild()

    def on_status(self, text):
        self.status.text = text

    def on_data(self, label, game):
        if self.hidden or (label is not None and label != self.label):
            return
        if game is None and label is not None:
            self.later(self.rebuild, 1.0)       # catalogue complet : nouvelle page
            return
        if label is None or self.sort_index in (1, 2) or self.filter_index:
            self.later(self.rebuild, 1.0)  # l'ordre ou le filtre peut changer
            return
        self.update_summary()
        self.redraw_game(game)

    def on_theme(self):
        """Nouveau thème : les jaquettes visibles reprennent la bonne transparence."""
        for v in list(self.live.values()) + self.pool:
            if isinstance(v, Tile):
                v.t_last.clear()
        for i, v in list(self.live.items()):
            if isinstance(v, Tile) and v.t_game:
                v.t_fill(self.label, v.t_game, self.frames[i])

    def on_cover(self, url):
        if self.hidden:
            return
        for i, v in list(self.live.items()):
            kind, game = self.items[i]
            if kind == "g" and isinstance(v, Tile) and self.app.cover_url(self.label, game) == url:
                v.t_show_cover()

    # ---------------------------------------------------------- contrôles
    def textfield_did_change(self, tf):
        self.query = tf.text or ""
        self._later = None
        self.later(self.rebuild, 0.25)       # pas de recalcul à chaque lettre

    def textfield_should_return(self, tf):
        tf.end_editing()
        return True

    def filter_changed(self, sender):
        self.filter_index = sender.selected_index
        self.rebuild()

    def scope_changed(self, sender):
        self.complete = sender.selected_index == 1
        if self.complete:
            self.app.full.compact(self.label, self.app.matched_titles(self.label))
            self.app.full_wanted.add(self.label)
            self.app.wake.set()
        self.rebuild()

    def quick_changed(self, sender):
        self.quick = sender.selected_index == 1

    def cycle_sort(self):
        self.sort_index = (self.sort_index + 1) % len(SORTS)
        self.bar_button = ("Trier : " + SORTS[self.sort_index], lambda s: self.cycle_sort())
        self.nav._update_bar()
        self.rebuild()

    # ---------------------------------------------------------- données affichées
    def update_summary(self):
        got, total = self.app.coll.count(self.label), len(GAMES_BY[self.label])
        value, known = self.app.console_value(self.label)
        txt = "%d / %d obtenus" % (got, total)
        if got:
            txt += "   •   valeur %s" % eur(value)
        if self.complete:
            d = self.app.full.get(self.label)
            txt += "   •   +%d jeux%s" % (len(d["rows"]), "" if d.get("done") else "…")
        self.summary.text = txt

    def matching(self):
        q = normalize(self.query.strip())
        owned = self.app.coll.owned[self.label]
        f = FILTERS[self.filter_index]
        out = []
        pool = list(GAMES_BY[self.label])
        if self.complete:
            pool += self.app.full.names(self.label)
        seen = set(pool)
        pool += [g for g in sorted(owned) if g not in seen]
        for g in pool:
            if f == "Obtenus" and g not in owned:
                continue
            if f == "Manquants" and g in owned:
                continue
            if q and q not in normalize(g) and \
                    q not in normalize(self.app.section(self.label, g)):
                continue
            out.append(g)
        return out

    def rebuild(self):
        games_list = self.matching()
        games = set(games_list)
        items = []
        if self.sort_index == 0:  # ordre du catalogue, avec les titres de section
            seen = set()
            extra = [g for g in games_list if g not in SEL_SET[self.label]]
            sections = list(SECTIONS_BY[self.label])
            if extra:
                sections.append(("Tous les autres jeux", extra))
            for section, sgames in sections:
                shown = [g for g in sgames if g in games and g not in seen]
                if not shown:
                    continue
                got = sum(1 for g in sgames if g in self.app.coll.owned[self.label])
                items.append(("h", "%s  (%d/%d)" % (section, got, len(sgames))))
                for g in shown:
                    seen.add(g)
                    items.append(("g", g))
        else:
            lst = list(games_list)
            if self.sort_index == 1:
                lst.sort(key=lambda g: -((self.app.price(self.label, g) or {}).get("mid") or -1))
            elif self.sort_index == 2:
                lst.sort(key=lambda g: -((self.app.price(self.label, g, "Disque seul") or {})
                                         .get("mid") or -1))
            else:
                lst.sort(key=normalize)
            items = [("g", g) for g in lst]
        self.items = items
        self.compute_frames()
        self.update_summary()

    def compute_frames(self):
        w = self.scroll.width
        if w < 50:
            return
        self.layout_width = w
        pad = 10
        cols = max(3, int((w - pad) // 125))
        tw = (w - pad * (cols + 1)) / cols
        th = tw * 1.42 + 52
        self.tile_size = (tw, th)
        frames, x_i, y = [], 0, pad
        for kind, _ in self.items:
            if kind == "h":
                if x_i:
                    y += th + pad
                    x_i = 0
                frames.append((pad, y, w - 2 * pad, 28))
                y += 32
            else:
                frames.append((pad + x_i * (tw + pad), y, tw, th))
                x_i += 1
                if x_i == cols:
                    x_i = 0
                    y += th + pad
        if x_i:
            y += th + pad
        if not self.items:
            frames = []
            y = 200
        self.frames = frames
        self.tops = [f[1] for f in frames]
        for i in list(self.live):
            self.release(i)
        self.empty_label_visible(not self.items)
        self.scroll.content_size = (w, y + pad)
        off = self.scroll.content_offset[1]
        if off > max(0, y - self.scroll.height):
            self.scroll.content_offset = (0, 0)
        self.render_visible()

    def empty_label_visible(self, show):
        if not hasattr(self, "empty"):
            self.empty = make_label("Aucun jeu ne correspond.", (0, 60, 10, 30), 15, False,
                                    self.app.theme["sub"], "center")
            self.scroll.add_subview(self.empty)
        self.empty.frame = (0, 60, self.scroll.width, 30)
        self.empty.hidden = not show

    def scrollview_did_scroll(self, sv):
        self.app.user_busy_until = time.time() + 0.8   # le chargement laisse la priorité
        self.render_visible()

    def indices_between(self, y0, y1):
        """Cases dont le haut est entre y0 et y1 (recherche rapide : les cases sont
        rangées de haut en bas)."""
        import bisect
        tile_h = getattr(self, "tile_size", (0, 300))[1]
        start = bisect.bisect_left(self.tops, y0 - tile_h)
        end = bisect.bisect_right(self.tops, y1)
        return range(start, end)

    def render_visible(self):
        """Affiche les cases à l'écran (+ une petite marge), recycle les autres, et
        demande le téléchargement des seules jaquettes à l'écran puis juste après."""
        off, h = self.scroll.content_offset[1], self.scroll.height
        rng = self.indices_between(off - 150, off + h + 250)
        key = (rng.start, rng.stop, len(self.items))
        if key == getattr(self, "last_rng", None) and len(self.live) == len(rng):
            return                       # mêmes cases à l'écran : rien à refaire
        self.last_rng = key
        need = set(rng)
        for i in list(self.live):
            if i not in need:
                self.release(i)
        for i in sorted(need):
            if i not in self.live:
                self.live[i] = self.make_view(i)
        # Fenêtre de préchargement : l'écran, puis 1 écran plus bas et ½ écran plus haut.
        visible = list(self.indices_between(off, off + h))
        around = list(self.indices_between(off + h, off + 2 * h)) + \
            list(self.indices_between(off - h / 2, off))
        self.prefetch = [i for i in around if self.items[i][0] == "g"]
        window = [self.app.cover_url(self.label, self.items[i][1])
                  for i in visible + self.prefetch if self.items[i][0] == "g"]
        if window != getattr(self, "last_window", None):
            self.last_window = window
            self.app.covers.set_window(window)

    def release(self, i):
        v = self.live.pop(i, None)
        if v is None:
            return
        if isinstance(v, Tile):
            v.t_release()
            self.pool.append(v)
        else:
            self.scroll.remove_subview(v)

    def idle(self):
        """Temps mort (4 fois par seconde) : décode à l'avance 3 jaquettes de la zone
        juste à côté de l'écran, pour qu'elles s'affichent instantanément."""
        done = 0
        for i in getattr(self, "prefetch", []):
            if done >= 3:
                break
            kind, game = self.items[i] if i < len(self.items) else ("h", None)
            if kind != "g":
                continue
            url = self.app.cover_url(self.label, game)
            if not url:
                continue
            owned = self.app.coll.is_owned(self.label, game)
            p = self.app.covers.path(url, grey=not owned)
            if p in IMAGE_CACHE or not CoverStore.has_file(p):
                continue
            load_image(p)
            done += 1

    def redraw_index(self, i):
        v = self.live.get(i)
        if isinstance(v, Tile) and self.items[i][0] == "g":
            v.t_fill(self.label, self.items[i][1], self.frames[i])
        elif v is not None:
            self.release(i)
            self.live[i] = self.make_view(i)

    def redraw_game(self, game):
        for i, (kind, g) in enumerate(self.items):
            if kind == "g" and g == game:
                self.redraw_index(i)

    def make_view(self, i):
        kind, value = self.items[i]
        frame = self.frames[i]
        if kind == "h":
            v = make_label(value.upper(), frame, 12, True, self.app.theme["sub"])
            self.scroll.add_subview(v)
            return v
        tile = self.pool.pop() if self.pool else None
        if tile is None:
            tile = Tile(self.app, self.tapped)
            self.scroll.add_subview(tile)
        tile.hidden = False
        tile.t_fill(self.label, value, frame)
        return tile

    def tapped(self, game):
        if self.quick:
            now = self.app.toggle(self.label, game)
            hud(("✓ " if now else "✗ ") + game, "success", 0.5)
            if self.filter_index:
                self.rebuild()
            return
        self.nav.push(DetailScreen(self.app, self.nav, self.label, game))

    def layout(self):
        w, h = self.width, self.height
        y = 8
        self.search.frame = (10, y, w - 20, 34)
        y += 40
        self.filter_ctrl.frame = (10, y, w - 20, 30)
        y += 36
        self.scope_ctrl.frame = (10, y, w - 20, 30)
        y += 36
        self.quick_ctrl.frame = (10, y, w - 20, 30)
        y += 36
        self.summary.frame = (12, y, w - 24, 18)
        y += 18
        self.status.frame = (12, y, w - 24, 16)
        y += 18
        self.scroll.frame = (0, y, w, max(0, h - y))
        if abs(self.layout_width - w) > 1:
            self.compute_frames()


@guard_class
class Tile(ui.View):
    """Une case du « Pokédex » : jaquette (grise si pas obtenu), n°, nom, prix, rareté.
    Les cases sont RECYCLÉES : en faisant défiler, on change juste leur contenu."""

    def __init__(self, app, on_tap):
        super().__init__()
        t = app.theme
        self.t_app, self.t_on_tap, self.t_game, self.t_size = app, on_tap, None, None
        self.t_last = {}
        self.background_color = t["card"]
        self.corner_radius = 10
        self.t_ph = ui.View()                      # couleur d'attente
        self.t_ph.corner_radius = 6
        self.t_ph_label = make_label("", (0, 0, 10, 10), 30, True, t["sub"], "center")
        self.t_ph.add_subview(self.t_ph_label)
        self.t_img = ui.ImageView()
        self.t_img.content_mode = ui.CONTENT_SCALE_ASPECT_FIT
        # Numéro : fond foncé + léger contour clair, lisible même sur la bande noire
        # en haut des jaquettes PS2.
        self.t_num_box, self.t_num = make_pill("", (8, 8, 44, 18), 10, (0, 0, 0, 0.75),
                                               radius=6)
        self.t_num_box.border_width = 1
        self.t_num_box.border_color = (1, 1, 1, 0.45)
        self.t_ok_box, self.t_ok = make_pill("✓", (0, 8, 24, 24), 14, t["owned"])
        self.t_title = make_label("", (0, 0, 10, 10), 11, False, t["text"], "center", 2)
        self.t_price = make_label("", (0, 0, 10, 10), 11, True, t["text"])
        self.t_stars = make_label("", (0, 0, 10, 10), 10, False, t["sub"], "right")
        self.t_delta = make_label("", (0, 0, 10, 10), 10, True, t["sub"], "center")
        self.t_btn = ui.Button()
        self.t_btn.action = lambda s: self.t_game and self.t_on_tap(self.t_game)
        for v in (self.t_ph, self.t_img, self.t_num_box, self.t_ok_box, self.t_title, self.t_price,
                  self.t_stars, self.t_delta,
                  self.t_btn):
            self.add_subview(v)

    def t_place(self, w, h):
        cover_h = h - 52
        self.t_ph.frame = self.t_img.frame = (5, 5, w - 10, cover_h - 5)
        self.t_ph_label.frame = (0, (cover_h - 5) / 2 - 20, w - 10, 40)
        self.t_ok_box.frame = (w - 32, 8, 24, 24)
        self.t_title.frame = (5, cover_h + 2, w - 10, 30)
        self.t_price.frame = (6, h - 19, w * 0.36, 15)
        self.t_delta.frame = (w * 0.28, h - 19, w * 0.46, 15)
        self.t_stars.frame = (w * 0.7 - 6, h - 19, w * 0.3, 15)
        self.t_btn.frame = (0, 0, w, h)
        self.t_size = (w, h)

    def t_set(self, view, attr, value):
        """Ne touche une propriété iOS que si sa valeur change : chaque modification
        traverse le pont Python → iOS, coûteux pendant le défilement."""
        k = (id(view), attr)
        if self.t_last.get(k, self) != value:
            self.t_last[k] = value
            setattr(view, attr, value)

    def t_fill(self, label, game, frame):
        app, t = self.t_app, self.t_app.theme
        sv = self.t_set
        sv(self, "frame", frame)
        if self.t_size != (frame[2], frame[3]):
            self.t_place(frame[2], frame[3])
        self.t_console, self.t_game = label, game
        owned = app.coll.is_owned(label, game)
        rar = app.rarity(label, game)
        price = app.price(label, game)
        sv(self, "border_width", 2 if owned else 0.5)
        sv(self, "border_color", (rar[3] if rar else t["owned"]) if owned else t["line"])
        sv(self.t_num, "text", "#%03d" % app.num(label, game))
        sv(self.t_ok_box, "hidden", not owned)
        sv(self.t_title, "text", game)
        sv(self.t_title, "font", ("<System-Bold>" if owned else "<System>", 11))
        sv(self.t_title, "text_color", t["text"] if owned else t["sub"])
        if price:
            ptxt = ("✎ " if price.get("manual") else "") + eur_short(price["mid"])
        else:
            ptxt = "prix ?" if app.error_of(label, game) else "…"
        sv(self.t_price, "text", ptxt)
        dtxt, dcol = delta_text(app.delta(label, game), short=True)
        sv(self.t_delta, "text", dtxt)
        sv(self.t_delta, "text_color", dcol)
        sv(self.t_stars, "text", "★" * rar[2] if rar else "")
        sv(self.t_stars, "text_color", rar[3] if rar else t["sub"])
        self.t_show_cover()

    def t_cover_path(self):
        """(chemin de l'image, atténuer ?) ou (None, False) si pas encore téléchargée."""
        app = self.t_app
        owned = app.coll.is_owned(self.t_console, self.t_game)
        url = app.cover_url(self.t_console, self.t_game)
        if not url:
            return None, False
        p = app.covers.path(url, grey=not owned)
        if CoverStore.has_file(p):
            return p, False
        if not owned and app.covers.has(url):
            return app.covers.path(url), True      # pas de version grise : couleur atténuée
        return None, False

    def t_show_cover(self):
        app, t = self.t_app, self.t_app.theme
        owned = app.coll.is_owned(self.t_console, self.t_game)
        path, dim = self.t_cover_path()
        img = load_image(path) if path else None
        if img:
            self.t_img.image = img
            dark = t.get("style") == "dark"   # sur fond noir, une jaquette grise doit rester visible
            self.t_img.alpha = 1.0 if owned else ((0.5 if dark else 0.35) if dim else
                                                  (0.8 if dark else 0.55))
            self.t_img.hidden = False
            self.t_ph.hidden = True
            return
        self.t_img.image = None                     # rien en mémoire pour cette case
        self.t_img.hidden = True
        self.t_ph.hidden = False
        url = app.cover_url(self.t_console, self.t_game)
        color = app.covers.color(url, grey=not owned)
        self.t_ph.background_color = color or t["placeholder"]
        self.t_ph.alpha = 1.0 if owned or not color else (0.8 if t.get("style") == "dark" else 0.55)
        loading = app.loading == (self.t_console, self.t_game) or (url and not color)
        self.t_ph_label.text = "" if color else ("…" if loading or not app.error_of(
            self.t_console, self.t_game) else "?")

    def t_release(self):
        """Case sortie de l'écran : on décharge son image et on la garde pour plus tard."""
        self.t_img.image = None
        self.t_game = None
        self.hidden = True


# ====================================================================== fiche d'un jeu
@guard_class
class DetailScreen(Screen):
    def __init__(self, app, nav, label, game):
        super().__init__()
        self.app, self.nav, self.label, self.game = app, nav, label, game
        self.screen_title = "#%03d  %s" % (app.num(label, game), label)
        self.background_color = app.theme["bg"]
        self.scroll = ui.ScrollView()
        self.scroll.indicator_style = app.theme["indicator"]
        self.scroll.always_bounce_vertical = True
        self.add_subview(self.scroll)

    def on_show(self):
        e = self.app.prices.get(key_of(self.label, self.game)) or {}
        if not self.app.prices.is_fresh(key_of(self.label, self.game)) or e.get("partial"):
            self.app.priority = (self.label, self.game)  # ventes détaillées en priorité
            self.app.wake.set()
        self.build()

    def on_hide(self):
        if self.app.priority == (self.label, self.game):
            self.app.priority = None

    def on_data(self, label, game):
        if not self.hidden and (label is None or (label == self.label and game == self.game)):
            self.later(self.build, 0.2)

    def on_cover(self, url):
        if url == self.app.cover_url(self.label, self.game) and not self.hidden:
            self.build()

    def layout(self):
        self.scroll.frame = (0, 0, self.width, self.height)
        self.build()

    def build(self):
        app, t, label, game = self.app, self.app.theme, self.label, self.game
        sv = self.scroll
        for v in list(sv.subviews):
            sv.remove_subview(v)
        w = self.width
        if w < 50:
            return
        pad = 16
        y = pad
        owned = app.coll.is_owned(label, game)
        rar = app.rarity(label, game)
        e = app.prices.get(key_of(label, game)) or {}

        # --- jaquette
        ch = min(300, w * 0.75)
        url = app.cover_url(label, game)
        img = load_image(app.covers.local(url)) if url else None
        if img:
            iv = ui.ImageView(frame=(pad, y, w - 2 * pad, ch))
            iv.content_mode = ui.CONTENT_SCALE_ASPECT_FIT
            iv.image = img
            sv.add_subview(iv)
        else:
            ph = ui.View(frame=((w - ch * 0.7) / 2, y, ch * 0.7, ch),
                         background_color=t["placeholder"])
            ph.corner_radius = 10
            ph.add_subview(make_label("Jaquette en cours de chargement" if not app.error_of(
                label, game) else "Pas de jaquette", (8, ch / 2 - 20, ch * 0.7 - 16, 40),
                13, False, t["sub"], "center", 2))
            sv.add_subview(ph)
        y += ch + 12

        # --- titre
        sv.add_subview(make_label(game, (pad, y, w - 2 * pad, 52), 20, True, t["text"],
                                  "center", 2))
        y += 54
        sv.add_subview(make_label("%s  •  %s" % (FULL_NAME[label], app.section(label, game)),
                                  (pad, y, w - 2 * pad, 18), 12, False, t["sub"], "center"))
        y += 24
        if rar:
            chip, _ = make_pill("%s  %s" % (stars(rar[2]), rar[1]), (w / 2 - 90, y, 180, 28), 13,
                                rar[3])
            sv.add_subview(chip)
            y += 34

        # --- je l'ai
        sv.add_subview(make_button("✓ Dans ma collection" if owned
                                   else "+ Je l'ai !", (pad, y, w - 2 * pad, 46),
                                   lambda s: self.toggle(),
                                   t["owned"] if owned else t["accent"], size=16))
        y += 50
        sv.add_subview(make_label("Toucher pour retirer de la collection" if owned else
                                  "Toucher pour l'ajouter à ta collection",
                                  (pad, y, w - 2 * pad, 14), 11, False, t["sub"], "center"))
        y += 22

        # --- condition
        sv.add_subview(make_label("Condition de mon exemplaire", (pad, y, w, 16), 12, False,
                                  t["sub"]))
        y += 18
        seg = ui.SegmentedControl(frame=(pad, y, w - 2 * pad, 32))
        seg.segments = list(COND)
        seg.selected_index = list(COND).index(app.coll.condition(label, game))
        seg.action = self.cond_changed
        sv.add_subview(seg)
        y += 44

        # --- prix
        card = ui.View(frame=(pad, y, w - 2 * pad, 10), background_color=t["card"])
        card.corner_radius = 12
        cy = 12
        cw = w - 2 * pad
        manual = app.coll.manual_price(label, game)
        fx = app.prices.fx_quick()
        cur = app.coll.condition(label, game)
        if manual is not None:
            card.add_subview(make_label("Mon prix : %s" % eur(manual), (14, cy, cw - 28, 24), 18,
                                        True, t["text"]))
            cy += 28
        if PriceCache.has_price(e):
            for c in COND:
                est = estimate(e, c, fx)
                bold = c == cur
                color = t["text"] if bold else t["sub"]
                size = 16 if bold else 14
                card.add_subview(make_label(("▶ " if bold else "") + c, (14, cy, cw * 0.6, 22),
                                            size, bold, color))
                card.add_subview(make_label(eur(est["mid"]) if est else "—",
                                            (cw * 0.5, cy, cw * 0.5 - 14, 22), size, bold, color,
                                            "right"))
                cy += 22
                if est and est["n"] >= 3:
                    card.add_subview(make_label(
                        "ventes récentes : %s – %s  (%s)" % (
                            eur_short(est["min"]), eur_short(est["max"]),
                            plural(est["n"], "vente")),
                        (14, cy, cw - 28, 16), 11, False, t["sub"]))
                    cy += 18
                cy += 6
            d = app.delta(label, game)
            if d:
                txt, col = delta_text(d)
                rec = app.coll.added.get(key_of(label, game)) or {}
                card.add_subview(make_label("Ajouté le %s à %s" % (
                    time.strftime("%d/%m/%Y", time.localtime(rec.get("ts", time.time()))),
                    eur(d[0])), (14, cy, cw * 0.6, 18), 12, False, t["sub"]))
                card.add_subview(make_label(txt, (cw * 0.55, cy, cw * 0.45 - 14, 18), 13, True,
                                            col, "right"))
                cy += 24
            info = "Fiche PriceCharting : %s" % (e.get("title") or "?")
            if e.get("region") == "US":
                info += " (version US : jeu non sorti en Europe)"
            if e.get("partial"):
                info += "\nVentes détaillées en cours de chargement..."
            else:
                info += "\nMis à jour le %s" % time.strftime("%d/%m/%Y", time.localtime(e["ts"]))
            card.add_subview(make_label(info, (14, cy + 4, cw - 28, 48), 11, False, t["sub"],
                                        lines=3))
            cy += 56
        else:
            err = app.error_of(label, game)
            card.add_subview(make_label(("Prix indisponible : " + err) if err else
                                        "Chargement du prix...", (14, cy, cw - 28, 48), 13,
                                        False, t["sub"], lines=3))
            cy += 52
        card.frame = (pad, y, cw, cy + 6)
        sv.add_subview(card)
        y += cy + 18

        # --- actions
        actions = [
            ("Saisir mon prix", self.ask_manual),
            ("Effacer mon prix" if manual is not None else "Recharger le prix",
             self.clear_manual if manual is not None else self.reload),
            ("eBay (vendus)", self.open_ebay),
            ("Leboncoin", self.open_lbc),
            ("PriceCharting", self.open_pc),
            ("Corriger la fiche", self.fix_url),
            ("Copier le nom", self.copy_name),
            ("Clé API (option)", self.ask_token),
        ]
        bw = (w - 2 * pad - 10) / 2
        for i, (title, fn) in enumerate(actions):
            x = pad + (i % 2) * (bw + 10)
            sv.add_subview(make_button(title, (x, y, bw, 40), (lambda s, fn=fn: fn()),
                                       t["card"], t["accent"], 13))
            if i % 2:
                y += 48
        y += pad
        sv.content_size = (w, y)

    # ---------------------------------------------------------- actions
    def toggle(self):
        now = self.app.toggle(self.label, self.game)
        hud("Ajouté à la collection" if now else "Retiré de la collection", "success", 0.7)

    def cond_changed(self, sender):
        self.app.coll.set_condition(self.label, self.game, list(COND)[sender.selected_index])
        self.app.save()
        self.app.notify(self.label, self.game)

    @background
    def ask_manual(self):
        cur = self.app.coll.manual_price(self.label, self.game)
        try:
            txt = console.input_alert(self.game, "Prix en euros (ex : 12,50)",
                                      ("%.2f" % cur).replace(".", ",") if cur is not None else "",
                                      "Enregistrer")
        except KeyboardInterrupt:
            return
        try:
            value = parse_euros(txt)
        except ValueError:
            alert("Prix invalide", "Écris un nombre positif, par exemple 12,50.")
            return
        self.app.coll.set_manual(self.label, self.game, value)
        self.app.save()
        self.app.notify(self.label, self.game)
        hud("Prix enregistré", "success", 0.8)

    def clear_manual(self):
        self.app.coll.set_manual(self.label, self.game, None)
        self.app.save()
        self.app.notify(self.label, self.game)

    def reload(self):
        self.app.refetch(self.label, self.game, full=True)
        hud("Prix redemandé", "success", 0.8)

    def open_ebay(self):
        q = "%s %s PAL" % (search_name(self.game), FULL_NAME[self.label])
        webbrowser.open("https://www.ebay.fr/sch/i.html?LH_Sold=1&LH_Complete=1&_nkw="
                        + quote_plus(q))

    def open_lbc(self):
        q = "%s %s" % (search_name(self.game), FULL_NAME[self.label])
        webbrowser.open("https://www.leboncoin.fr/recherche?text=" + quote_plus(q))

    def open_pc(self):
        webbrowser.open(self.app.prices.known_url(key_of(self.label, self.game))
                        or search_url(self.label, self.game))

    def copy_name(self):
        import clipboard
        clipboard.set(self.game)
        hud("Nom copié", "success", 0.8)

    @background
    def fix_url(self):
        e = self.app.prices.get(key_of(self.label, self.game)) or {}
        try:
            txt = console.input_alert(
                "Corriger la fiche",
                "Jeu trouvé : %s\n\nTouche « PriceCharting », trouve le bon jeu (version "
                "PAL), copie le lien de sa page et colle-le ici. Laisse vide pour revenir "
                "à la recherche automatique." % (e.get("title") or "aucun"),
                self.app.coll.fixed_url(self.label, self.game) or "", "Enregistrer")
        except KeyboardInterrupt:
            return
        txt = (txt or "").strip()
        m = re.search(r"pricecharting\.com(/game/[^\s?#]+)", txt)
        if txt and not m:
            alert("Lien invalide", "Le lien doit ressembler à :\n"
                  "https://www.pricecharting.com/game/pal-playstation-2/god-of-war")
            return
        self.app.coll.set_fixed_url(self.label, self.game, BASE + m.group(1) if m else None)
        self.app.save()
        self.app.refetch(self.label, self.game, full=True)
        hud("Fiche enregistrée" if m else "Recherche automatique", "success", 0.8)

    @background
    def ask_token(self):
        try:
            txt = console.input_alert(
                "Clé API PriceCharting",
                "Facultatif : tout fonctionne sans clé. Clé de ton abonnement PriceCharting "
                "(page Subscription). Laisse vide pour la supprimer.",
                read_token() or "", "Enregistrer")
        except KeyboardInterrupt:
            return
        txt = (txt or "").strip()
        try:
            write_token(txt)
        except OSError as ex:
            alert("Erreur", str(ex))
            return
        hud("Clé enregistrée" if txt else "Clé supprimée", "success", 0.8)


# ====================================================================== mise à jour (interface)
def apply_update(version, code):
    """Installe et prévient l'utilisateur ; renvoie True si c'est fait. (fil de fond)"""
    try:
        path = install_update(code)
    except Exception as ex:
        log_exception("Échec de l'installation de la mise à jour %s" % version)
        alert("La mise à jour a échoué",
              "%s\n\nSolution : relance la commande d'installation dans la console "
              "Pythonista (voir le README)." % ex)
        return False
    log("Mise à jour %s installée (%s)" % (version, path))
    alert("Mise à jour installée",
          "Version %s installée.\n\nFerme l'app (croix en haut à gauche) puis relance "
          "le script avec ▶." % version)
    return True


# ====================================================================== journal / diagnostic
def journal_actions():
    """Ajouts/retraits de jeux notés dans le journal : [(ajout ?, console, jeu)]."""
    out = []
    try:
        with open(LOG_FILE, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                m = re.search(r"Action : (ajout de|retrait de) (\S+) \| (.+)$", line.rstrip("\n"))
                if m:
                    out.append((m.group(1) == "ajout de", m.group(2), m.group(3)))
    except OSError:
        pass
    return out


def _tail(path, n):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            return "".join(f.readlines()[-n:]).rstrip()
    except OSError:
        return "(vide)"


def _device_info():
    info = []
    try:
        from objc_util import ObjCClass
        dev = ObjCClass("UIDevice").currentDevice()
        info.append("iOS %s (%s)" % (dev.systemVersion(), dev.model()))
        bundle = ObjCClass("NSBundle").mainBundle()
        info.append("Pythonista %s" % bundle.objectForInfoDictionaryKey_(
            "CFBundleShortVersionString"))
    except Exception:
        import platform
        info.append(platform.platform())
    info.append("Python %s" % sys.version.split()[0])
    return " • ".join(str(x) for x in info)


def diagnostic(app):
    """Rapport complet à copier/coller pour signaler un problème."""
    try:
        st = os.statvfs(DOCS)
        free = "%d Mo" % (st.f_bavail * st.f_frsize / 1e6)
    except Exception:
        free = "?"
    try:
        files = os.listdir(COVER_DIR)
        covers_mb = sum(os.path.getsize(os.path.join(COVER_DIR, f)) for f in files) / 1e6
        covers = "%d fichiers, %.1f Mo" % (len(files), covers_mb)
    except OSError:
        covers = "aucune"
    priced = sum(1 for l in LABELS for g in GAMES_BY[l] if app.entry(l, g))
    backups = list_backups()
    errors = [(l, g, app.error_of(l, g)) for l in LABELS for g in GAMES_BY[l]
              if app.error_of(l, g)]
    lines = [
        "=== RAPPORT – Ma collection de jeux ===",
        "Version du script : %s" % APP_VERSION,
        "Date : %s" % time.strftime("%d/%m/%Y %H:%M:%S"),
        "Appareil : %s" % _device_info(),
        "Stockage libre : %s" % free,
        "Jeux possédés : %d / %d (chargée depuis : %s)" % (
            sum(app.coll.count(l) for l in LABELS), sum(len(GAMES_BY[l]) for l in LABELS),
            app.coll.source),
        "Sauvegardes de la collection : %s" % (
            "%d (dernière : %s, %d jeux)" % (len(backups), time.strftime(
                "%d/%m %H:%M", time.localtime(backups[0][1])), backups[0][2])
            if backups else "aucune"),
        "Prix connus : %d / %d   •   jeux sans prix (erreur) : %d" % (
            priced, sum(len(GAMES_BY[l]) for l in LABELS), len(errors)),
        "Jaquettes : %s (file d'attente %d, échecs %d)" % (
            covers, len(app.covers.queue), len(app.covers.failed)),
        "Réseau : %s%s" % (NET.mode_text(), (", en pause %d min" % NET.blocked_minutes())
                           if NET.blocked_minutes() else ""),
        "Navigateur intégré : %s" % ("actif" if NET.web else "pas encore utilisé"),
        "État : %s" % (app.status or "—"),
    ]
    if errors:
        lines += ["", "--- Jeux sans prix (10 premiers) ---"]
        lines += ["%s | %s : %s" % e for e in errors[:10]]
    crash = crash_text()
    if crash:
        lines += ["", "--- Plantages durs ---", crash[-4000:]]
    important = [ln for ln in _tail(LOG_FILE, 5000).split("\n")
                 if "=====" in ln or " ALERTE " in ln or " CRASH " in ln or " ERREUR " in ln
                 or " GEL " in ln or "Action :" in ln]
    lines += ["", "--- Démarrages et problèmes importants (30 derniers) ---"]
    lines += important[-30:] or ["(aucun)"]
    lines += ["", "--- Journal (200 dernières lignes) ---", _tail(LOG_FILE, 200)]
    return "\n".join(lines)


@guard_class
class JournalScreen(Screen):
    screen_title = "Journal"

    def __init__(self, app, nav):
        super().__init__()
        self.app, self.nav = app, nav
        t = app.theme
        self.background_color = t["bg"]
        self.info = make_label("En cas de problème : « Copier le rapport » puis colle-le dans "
                               "la conversation avec Claude.", (0, 0, 10, 10), 12, False,
                               t["sub"], lines=2)
        self.add_subview(self.info)
        self.buttons = [
            make_button("Copier le rapport", (0, 0, 10, 10), lambda s: self.copy(),
                        t["accent"], size=13),
            make_button("Partager", (0, 0, 10, 10), lambda s: self.share(), t["field"],
                        t["accent"], 13),
            make_button("Effacer", (0, 0, 10, 10), lambda s: self.clear(), t["field"],
                        "#ff3b30", 13),
        ]
        self.update_btn = make_button("Rechercher une mise à jour (version %s)"
                                      % APP_VERSION.split(" ")[0], (0, 0, 10, 10),
                                      lambda s: self.check_update(), t["field"], t["accent"], 13)
        self.add_subview(self.update_btn)
        self.verify_btn = make_button("Faire la vérification PriceCharting", (0, 0, 10, 10),
                                      lambda s: self.verify(), t["field"], t["accent"], 13)
        self.add_subview(self.verify_btn)
        self.restore_btn = make_button("Restaurer une sauvegarde de ma collection", (0, 0, 10, 10),
                                       lambda s: self.restore(), t["field"], t["accent"], 13)
        self.add_subview(self.restore_btn)
        for b in self.buttons:
            self.add_subview(b)
        self.tv = ui.TextView()
        self.tv.editable = False
        self.tv.font = ("Menlo", 10)
        self.tv.background_color = t["card"]
        self.tv.text_color = t["text"]
        self.add_subview(self.tv)

    def on_show(self):
        self.tv.text = diagnostic(self.app)

    def layout(self):
        w, h = self.width, self.height
        self.info.frame = (14, 6, w - 28, 34)
        bw = (w - 40) / 3.0
        for i, b in enumerate(self.buttons):
            b.frame = (10 + i * (bw + 10), 44, bw, 34)
        self.update_btn.frame = (10, 86, w - 20, 34)
        self.verify_btn.frame = (10, 126, w - 20, 34)
        self.restore_btn.frame = (10, 166, w - 20, 34)
        self.tv.frame = (10, 208, w - 20, max(0, h - 218))

    @background
    def restore(self):
        import dialogs
        backups = list_backups()
        replay = journal_actions()
        items, actions = [], []
        for path, ts, count, reason in backups:
            items.append("%s – %d jeux (%s)" % (time.strftime("%d/%m %H:%M", time.localtime(ts)),
                                                 count, reason.replace("-", " ")))
            actions.append(("backup", path))
        if replay:
            items.append("Reconstituer depuis le journal (%d ajouts/retraits notés)" % len(replay))
            actions.append(("journal", None))
        if not items:
            alert("Aucune sauvegarde", "Il n'y a pas encore de sauvegarde ni d'action notée "
                  "dans le journal.")
            return
        choice = dialogs.list_dialog("Restaurer (actuellement %d jeux)" % self.app.coll.total(),
                                     items)
        if not choice:
            return
        kind, path = actions[items.index(choice)]
        try:
            console.alert("Restaurer ?", "%s\n\nTa collection actuelle est d'abord sauvegardée : "
                          "tu pourras revenir en arrière." % choice, "Restaurer")
        except KeyboardInterrupt:
            return
        backup_collection("avant-restauration")
        coll = self.app.coll
        if kind == "backup":
            data = read_collection_file(path)
            if data is None:
                alert("Sauvegarde illisible", os.path.basename(path))
                return
            with coll.lock:
                coll.owned = {label: set() for label in LABELS}
                coll.conditions, coll.manual, coll.urls, coll.added = {}, {}, {}, {}
                coll.apply(data)
        else:
            with coll.lock:
                for adding, label, game in replay:
                    if label not in coll.owned:
                        continue
                    if adding:
                        coll.owned[label].add(game)
                    else:
                        coll.owned[label].discard(game)
        self.app.save()
        log("Action : restauration (%s) -> %d jeux" % (choice, coll.total()), "ALERTE")
        self.app.notify()
        on_main(self.on_show)
        alert("Collection restaurée", "%d jeux dans ta collection." % coll.total())

    def verify(self):
        if NET.make_web_now() is None:
            hud("Navigateur intégré indisponible", "error", 1.5)
            return
        NET.web.open_manually()
        self.app.retry_now()

    @background
    def check_update(self):
        hud("Recherche...", "success", 0.6)
        try:
            found = check_update()
        except Exception as ex:
            log("Vérification de mise à jour impossible : %s" % ex, "AVERT")
            alert("Mise à jour", "Impossible de vérifier : %s" % ex)
            return
        if not found:
            alert("Mise à jour", "Tu as déjà la dernière version (%s)." % APP_VERSION)
            return
        self.app.update = found
        self.app.notify()
        try:
            console.alert("Mise à jour %s disponible" % found[0],
                          "Installer maintenant ? Ta collection est conservée.", "Installer")
        except KeyboardInterrupt:
            return
        if apply_update(found[0], found[1]):
            self.app.update = None

    def copy(self):
        import clipboard
        clipboard.set(diagnostic(self.app))
        hud("Rapport copié : colle-le dans la conversation", "success", 1.5)

    @background
    def share(self):
        import dialogs
        dialogs.share_text(diagnostic(self.app))

    @background
    def clear(self):
        try:
            console.alert("Effacer le journal ?", "Le rapport actuel sera perdu.", "Effacer")
        except KeyboardInterrupt:
            return
        for p in (LOG_FILE, CRASH_FILE):
            try:
                os.remove(p)
            except OSError:
                pass
        log("Journal effacé")
        on_main(self.on_show)


# ====================================================================== rapport de valeur
def compute_value(app, only):
    if app.busy:
        hud("Calcul déjà en cours...", "error", 1.0)
        return

    def work():
        app.busy = True
        try:
            labels = [only] if only else list(LABELS)
            if not any(app.coll.owned_games(l) for l in labels):
                alert("Collection vide", "Ajoute d'abord des jeux à ta collection.")
                return
            report = build_report(app, labels)
            on_main(show_text, app, "Valeur de la collection", report)
        except Exception as ex:
            log_exception("Erreur pendant le calcul de la valeur")
            alert("Erreur pendant le calcul", "%s\n\nDétails dans le journal." % ex)
        finally:
            app.busy = False
    run_named("calcul", work)


def build_report(app, labels):
    fx, note = app.prices.get_fx()
    keys = ("min", "mid", "max")
    total = dict.fromkeys(keys, 0.0)
    lines, rows, missing = [], [], []
    n_ok = 0
    for l in labels:
        sub = dict.fromkeys(keys, 0.0)
        block = []
        for g in app.coll.owned_games(l):
            cond = app.coll.condition(l, g)
            e = app.entry(l, g)
            manual = app.coll.manual_price(l, g)
            if manual is not None:
                est = {"min": manual, "max": manual, "mid": manual, "n": 0, "manual": True}
                cond_txt = "mon prix"
            else:
                est = estimate(e, cond, fx) if e else None
                cond_txt = cond
            if not est:
                if e:
                    why = "pas de cote pour cette condition"
                else:
                    why = app.error_of(l, g) or "prix en cours de chargement, réessaie bientôt"
                missing.append("• %s – %s [%s] : %s" % (l, g, cond, why))
                continue
            n_ok += 1
            for k in keys:
                sub[k] += est[k]
                total[k] += est[k]
            rar = app.rarity(l, g)
            detail = eur(est["mid"])
            if abs(est["max"] - est["min"]) >= 1:
                detail += "  (ventes %s – %s)" % (eur_short(est["min"]), eur_short(est["max"]))
            block.append("• %s [%s] %s: %s" % (g, cond_txt, ("%s " % ("★" * rar[2])) if rar else "",
                                                detail))
            rows.append([l, g, cond_txt, round(est["mid"], 2), round(est["min"], 2),
                         round(est["max"], 2), rar[1] if rar else "",
                         (e or {}).get("title", "") if not est["manual"] else "",
                         (e or {}).get("url", "") if not est["manual"] else ""])
        if block:
            lines.append("=== %s : %s ===" % (FULL_NAME[l], eur(sub["mid"])))
            lines += block + [""]
    head = ["VALEUR DE LA COLLECTION (versions PAL)",
            time.strftime("Calculé le %d/%m/%Y à %H:%M"),
            "Source : PriceCharting + mes prix  •  USD→EUR %s (%s)"
            % (("%.4f" % fx).replace(".", ","), note), "",
            "VALEUR ESTIMÉE : %s" % eur(total["mid"]),
            "Fourchette : %s – %s" % (eur(total["min"]), eur(total["max"])),
            "%s, %d sans prix" % (
                plural(n_ok, "jeu valorisé").replace("jeu valorisés", "jeux valorisés"),
                len(missing)), ""]
    if missing:
        lines += ["=== SANS PRIX (non comptés) ==="] + missing + [""]
    csv_note = "CSV : Documents/valeur_collection.csv"
    try:
        with open(CSV_FILE, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f, delimiter=";")  # « ; » : s'ouvre directement dans Excel/Numbers FR
            w.writerow(["console", "jeu", "condition", "prix_eur", "bas_eur", "haut_eur",
                        "rarete", "fiche_pricecharting", "url"])
            for r in rows:
                w.writerow([str(x).replace(".", ",") if isinstance(x, float) else x for x in r])
    except OSError as ex:
        csv_note = "CSV non écrit : %s" % ex
    return "\n".join(head + lines + [csv_note])


def show_text(app, title, text):
    tv = ui.TextView()
    tv.name = title
    tv.editable = False
    tv.font = ("<System>", 13)
    tv.background_color = app.theme["card"]
    tv.text_color = app.theme["text"]
    tv.text = text
    tv.present("sheet")


# ====================================================================== lancement
def write_marker(started):
    """Fichier « session en cours » : début et dernier signe de vie de l'app."""
    try:
        write_json(RUN_MARKER, {"start": started, "alive": time.time()})
    except OSError:
        pass


def main():
    try:
        sys.setswitchinterval(0.002)   # l'interface récupère la main plus vite
    except Exception:
        pass
    install_crash_handlers()
    interrupted = os.path.exists(RUN_MARKER)
    previous = read_json(RUN_MARKER) if interrupted else None
    poison = None
    if interrupted:
        try:
            with open(JOB_FILE, "r", encoding="utf-8") as f:
                poison = f.read().strip()
        except OSError:
            pass
    # Plantage « tôt » = la session précédente a duré moins de 15 s
    # (signe de vie noté à 2 s, puis toutes les 10 s).
    early = isinstance(previous, dict) and \
        previous.get("alive", 0) - previous.get("start", 0) < 15
    starts = read_json(STARTS_FILE)
    count = (starts.get("early", 0) if isinstance(starts, dict) else 0) + 1 if early else 0
    try:
        write_json(STARTS_FILE, {"early": count})
    except OSError:
        pass
    write_marker(time.time())
    log("===== Démarrage version %s • %s =====" % (APP_VERSION, _device_info()))
    if interrupted:
        log("La session précédente ne s'est pas fermée normalement "
            "(plantage, ou Pythonista fermé de force)%s"
            % (" après moins de 15 s (%d fois de suite)" % count if early else ""), "ALERTE")
    try:
        app = App()
        backup_collection("lancement")       # copie de sécurité à chaque lancement
        app.interrupted = interrupted
        app.safe_mode = count >= 2
        if poison:
            app.set_poison(poison)
        try:
            os.remove(JOB_FILE)
        except OSError:
            pass
        root = AppView(app)
        root.push(HomeScreen(app, root))
        root.present("fullscreen", title_bar_color=app.theme["header"],
                     title_color=app.theme["text"])
        app.start()
    except Exception:
        log_exception("Plantage au démarrage")
        try:
            console.alert("Plantage au démarrage",
                          "Le détail est enregistré dans Documents/journal_collection.txt. "
                          "Ouvre ce fichier dans Pythonista et copie son contenu à Claude.",
                          "OK", hide_cancel_button=True)
        except Exception:
            pass
        raise


if __name__ == "__main__":
    main()
