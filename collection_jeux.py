# -*- coding: utf-8 -*-
"""
Ma collection de jeux – checklist multi-consoles pour Pythonista (iPhone / iPad)

Consoles : PS2, N64, DS, 3DS, Xbox 360, Wii, GameCube, Switch.

Utilisation :
  * Mode « Cocher » : toucher un jeu le coche / décoche (sauvegarde automatique).
  * Mode « Infos & prix » : toucher un jeu ouvre son menu (prix détaillé,
    condition, mon prix, corriger la fiche, eBay, Leboncoin...).

Prix (sans clé API, automatique) :
  * Les prix viennent de PriceCharting (versions PAL, en dollars convertis en euros).
  * Ils se chargent TOUT SEULS en arrière-plan, un jeu à la fois et à un rythme
    tranquille (≈ 1 requête toutes les 4 s) : d'abord les jeux affichés en mode
    « Infos & prix », puis tous les jeux possédés. Un prix est gardé 30 jours.
  * Prix affiché = la cote PriceCharting (calculée sur les ventes réelles eBay).
    Fourchette = ventes récentes (quart le moins cher → quart le plus cher).
  * Si le site bloque les requêtes du script, l'app bascule toute seule sur un
    navigateur intégré invisible (le même moteur que Safari).
  * Mauvais jeu trouvé ? Menu du jeu > « Corriger la fiche PriceCharting ».
  * Tu peux toujours saisir ton propre prix : il est prioritaire.
  * Clé API PriceCharting (abonnement) facultative : menu d'un jeu > « Clé API ».

Fichiers (dans Documents/) :
  collection_jeux.json      jeux possédés, conditions, prix saisis, fiches corrigées
                            (migration automatique depuis l'ancien collection_ps2.json)
  prix_cache.json           prix déjà chargés
  pricecharting_token.txt   clé API PriceCharting (facultative)
  valeur_collection.csv     export de la valeur de la collection
  debug_pricecharting.html  dernière page non reconnue (pour diagnostic)
"""

import csv
import html as htmllib
import json
import os
import random
import re
import threading
import time
import unicodedata
import webbrowser
from urllib.parse import quote_plus, urlencode

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

CACHE_VERSION = 2           # change si le format du cache change (l'ancien est ignoré)
CACHE_TTL = 30 * 24 * 3600  # un prix est gardé 30 jours (les cotes bougent peu)
ERR_TTL = 6 * 3600          # après un échec sur un jeu, nouvel essai automatique 6 h plus tard
MIN_GAP = 3.5               # au moins 3,5 s (+ 0 à 1,5 s au hasard) entre deux requêtes
BLOCK_PAUSE = 30 * 60       # pause si même le navigateur intégré est bloqué
WEB_TIMEOUT = 35            # délai max de chargement d'une page dans le navigateur intégré
DEFAULT_FX = 0.92           # taux USD→EUR de secours si hors ligne
BASE = "https://www.pricecharting.com"

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
]
LABELS = [c[0] for c in CONSOLES]
FULL_NAME = {c[0]: c[1] for c in CONSOLES}
SECTIONS_BY = {c[0]: c[2] for c in CONSOLES}
PC = {c[0]: (c[3], c[4]) for c in CONSOLES}
# Un jeu présent dans plusieurs sections d'une même console ne compte qu'une fois.
GAMES_BY = {
    c[0]: list(dict.fromkeys(g for _, games in c[2] for g in games)) for c in CONSOLES
}

# Noms à chercher sur PriceCharting quand le titre du catalogue est en français
# ou différent du titre PAL anglais utilisé par le site.
SEARCH_ALIASES = {}

# condition : (id de la cote sur la page du jeu, bloc des ventes, champ API, colonne recherche)
COND = {
    "Disque seul": ("used_price", "used", "loose-price", "used_price"),
    "Complet": ("complete_price", "cib", "cib-price", "cib_price"),
    "Neuf": ("new_price", "new", "new-price", "new_price"),
}
DEFAULT_COND = "Disque seul"
FILTERS = ["Tous", "À acheter", "Possédés"]
MODE_CHECK, MODE_INFO = 0, 1


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


def normalize(text):
    """Pour la recherche : « okami » trouve « Ōkami », « pokemon » trouve « Pokémon »."""
    return strip_accents(text.replace("’", "'")).casefold()


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


def hud(message, icon="success", duration=1.0):
    try:
        console.hud_alert(message, icon, duration)
    except Exception:
        pass


def run_thread(fn, *args):
    t = threading.Thread(target=fn, args=args)
    t.daemon = True
    t.start()
    return t


def on_main(fn, *args):
    """Exécute fn sur le fil de l'interface (obligatoire pour toucher aux vues)."""
    ui.delay(lambda: fn(*args), 0)


# ====================================================================== collection
class Collection:
    """Jeux possédés, condition par jeu, prix saisis à la main, fiches corrigées."""

    def __init__(self):
        self.lock = threading.RLock()
        self.owned = {label: set() for label in LABELS}
        self.conditions = {}
        self.manual = {}
        self.urls = {}  # fiche PriceCharting choisie à la main : "PS2|jeu" -> url
        self.load()

    def load(self):
        data = read_json(DATA_FILE)
        if isinstance(data, dict):
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
            urls = data.get("_urls")
            if isinstance(urls, dict):
                self.urls = {k: v for k, v in urls.items()
                             if isinstance(k, str) and isinstance(v, str) and "/game/" in v}
            return
        legacy = read_json(LEGACY_FILE)  # ancienne version (PS2 seule)
        if isinstance(legacy, list):
            self.owned["PS2"].update(g for g in legacy if isinstance(g, str))
        else:
            self.owned["PS2"].add("BLACK")  # premier lancement : BLACK déjà possédé
        self.save()

    def save(self):
        """Renvoie None si tout va bien, sinon le message d'erreur."""
        with self.lock:
            payload = {k: sorted(v) for k, v in self.owned.items()}
            payload["_conditions"] = dict(self.conditions)
            payload["_manual"] = dict(self.manual)
            payload["_urls"] = dict(self.urls)
            try:
                write_json(DATA_FILE, payload, indent=2)
            except OSError as e:
                return str(e)
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
        """Jeux possédés de la liste, dans l'ordre du catalogue."""
        s = self.owned[label]
        return [g for g in GAMES_BY[label] if g in s]

    def count(self, label):
        return len(self.owned_games(label))

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
    t = text[:5000] if text else ""
    return (status in (403, 503) and ("cf-" in t or "cloudflare" in t.lower())) \
        or "<title>Just a moment" in t or "challenge-platform" in t


class WebFetcher:
    """Navigateur intégré invisible (moteur Safari). Il exécute le JavaScript et passe
    les vérifications anti-robot que le module requests ne passe pas."""

    def __init__(self, host):
        self.wv = ui.WebView(frame=(0, 0, 4, 4))
        self.wv.touch_enabled = False
        self.wv.alpha = 0.02
        self.wv.scales_page_to_fit = False
        host.add_subview(self.wv)
        try:
            host.send_to_back(self.wv)
        except Exception:
            pass

    def _js(self, code):
        try:
            return self.wv.eval_js(code) or ""
        except Exception:
            return ""

    def get(self, url):
        self._js("window.__cj_old = 1;")  # repère : disparaît quand la nouvelle page est chargée
        on_main(self.wv.load_url, url)
        start = time.time()
        time.sleep(1.0)
        while time.time() - start < WEB_TIMEOUT:
            ready = self._js("(typeof window.__cj_old === 'undefined' && "
                             "document.readyState === 'complete') ? 'ok' : ''")
            if ready == "ok":
                title = self._js("document.title")
                if "Just a moment" not in title:
                    time.sleep(0.3)
                    page = self._js("document.documentElement.outerHTML")
                    href = self._js("location.href") or url
                    if page:
                        return href, page
            time.sleep(0.7)
        raise Blocked("le navigateur intégré n'a pas pu charger la page (vérification "
                      "anti-robot trop longue ou pas de connexion)")


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

    def _pace(self):
        wait = self.last_request + MIN_GAP + random.uniform(0, 1.5) - time.time()
        if wait > 0:
            time.sleep(wait)
        self.last_request = time.time()

    def _requests_get(self, url):
        import requests
        last_error = None
        for attempt in range(2):
            if attempt:
                time.sleep(5)
            self._pace()
            try:
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

    def get(self, url, params=None):
        """Renvoie (url finale, html)."""
        if params:
            url = url + ("&" if "?" in url else "?") + urlencode(params)
        with self.lock:
            mins = self.blocked_minutes()
            if mins:
                raise Blocked("PriceCharting est en pause encore %d min" % mins)
            if not self.use_web:
                try:
                    return self._requests_get(url)
                except Blocked:
                    if self.web is None:
                        self.blocked_until = time.time() + BLOCK_PAUSE
                        raise
                    self.use_web = True  # bascule sur le navigateur intégré
            self._pace()
            try:
                final, page = self.web.get(url)
            except Blocked:
                self.blocked_until = time.time() + BLOCK_PAUSE
                raise
            if is_challenge(200, page):
                self.blocked_until = time.time() + BLOCK_PAUSE
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
        results.append({"url": url.split("?")[0], "title": _clean_text(m.group(2)),
                        "guide": guide})
    return results


def parse_game_page(page):
    """Page d'un jeu : nom, cotes et ventes eBay réalisées par condition."""
    m = re.search(r'<h1 id="product_name"[^>]*>(.*?)<a', page, re.S)
    title = _clean_text(m.group(1)) if m else ""

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
    return title, guide, sales


# ---------------------------------------------------------------- choix du bon jeu
ROMAN = {"i": "1", "ii": "2", "iii": "3", "iv": "4", "v": "5", "vi": "6", "vii": "7",
         "viii": "8", "ix": "9", "x": "10", "xi": "11", "xii": "12", "xiii": "13"}
STOP = {"the", "a", "an", "of", "and", "de", "la", "le", "les", "du", "des", "et"}
EDITION = {"platinum", "essentials", "classics", "greatest", "hits", "selects", "players",
           "player", "choice", "edition", "special", "limited", "collectors", "collector",
           "steelbook", "version", "budget", "best", "favourites", "favorites", "pal",
           "uk", "fr", "french", "german", "italian", "spanish", "value", "nintendo",
           "playstation", "ps2", "wii", "xbox", "360", "ds", "3ds", "gamecube", "switch",
           "n64", "game", "video", "standard", "reprint", "new"}
BAD = {"demo", "promo", "manual", "guide", "strategy", "case", "only", "soundtrack",
       "amiibo", "controller", "bundle", "console", "system", "pack", "box", "art",
       "poster", "not", "resale", "disc", "cover", "sleeve", "kiosk", "trial"}


def title_tokens(s):
    s = normalize(s).replace("&", " and ").replace("'", "")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return [ROMAN.get(t, t) for t in s.split() if t not in STOP]


def match_score(wanted, candidate):
    w, c = set(title_tokens(wanted)), set(title_tokens(candidate))
    if not w or not c:
        return 0.0
    common = len(w & c)
    if not common:
        return 0.0
    missing = w - c
    penalty = 0.0
    for t in c - w:
        if t in BAD:
            penalty += 2.0
        elif t.isdigit():
            penalty += 1.5   # « Halo 3 » ≠ « Halo 4 »
        elif t in EDITION:
            penalty += 0.15  # « Platinum » : même jeu, réédition
        else:
            penalty += 1.0
    penalty += sum(1.5 if t.isdigit() else 1.0 for t in missing)
    return common / (len(w) + penalty)


def best_match(game, results):
    names = [search_name(game)] + [p.strip() for p in game.split(" / ")[1:]]
    best, best_score = None, 0.0
    for r in results:
        score = max(match_score(n, r["title"]) for n in names)
        if score > best_score:
            best, best_score = r, score
    return (best, best_score) if best_score >= 0.55 else (None, best_score)


# ---------------------------------------------------------------- récupération d'un prix
def _entry(url, title, guide, sales, partial):
    return {"v": CACHE_VERSION, "ts": time.time(), "url": url, "title": title,
            "guide": guide, "sales": sales, "partial": partial}


def fetch_game_page(url):
    final, page = NET.get(url)
    title, guide, sales = parse_game_page(page)
    if not any(guide.values()) and not any(sales.values()):
        save_debug(page)
        raise PriceError("page lue mais prix non reconnus (voir debug_pricecharting.html)")
    return _entry(final.split("?")[0], title, guide, sales, False)


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


def fetch_prices(label, game, fixed_url=None, known_url=None, full=False, token=None):
    """Prix d'un jeu.
    - fiche connue (corrigée à la main ou trouvée avant) : 1 requête sur la page du jeu ;
    - sinon : 1 recherche, qui contient déjà les cotes de chaque résultat ;
      full=True ajoute la page du jeu (ventes détaillées)."""
    if token and not fixed_url:
        return fetch_api(label, game, token)
    url = fixed_url or known_url
    if url:
        return fetch_game_page(url)
    slug, pcname = PC[label]
    final, page = NET.get(search_url(label, game))
    if "/game/%s/" % slug in final:  # le site a redirigé directement vers le jeu
        title, guide, sales = parse_game_page(page)
        if any(guide.values()) or any(sales.values()):
            return _entry(final.split("?")[0], title, guide, sales, False)
    results = parse_search(page, slug)
    best, _ = best_match(game, results)
    if not best:
        if not results and "product-" not in page:
            save_debug(page)
        raise PriceError("introuvable sur PriceCharting (%s). Utilise « Corriger la fiche "
                         "PriceCharting » pour choisir le bon jeu." % pcname)
    if full or not any(best["guide"].values()):
        return fetch_game_page(best["url"])
    return _entry(best["url"], best["title"], best["guide"], {}, True)


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
        b = self.data.get("_blocked_until")
        if isinstance(b, (int, float)) and b > time.time():
            NET.blocked_until = b  # la pause survit à la fermeture de l'app

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
            self.data["_blocked_until"] = NET.blocked_until
            try:
                write_json(CACHE_FILE, dict(self.data))
            except (OSError, TypeError, ValueError):
                pass

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
        if isinstance(err_ts, (int, float)) and now - err_ts < ERR_TTL:
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


# ====================================================================== thème
def make_theme():
    dark = False
    try:
        dark = ui.get_ui_style() == "dark"
    except Exception:
        pass
    if dark:
        return {"bg": "#1c1c1e", "field": "#2c2c2e", "text": "#f2f2f7", "sub": "#98989f",
                "owned": "#32d74b", "bar": "#2c2c2e", "accent": "#0a84ff",
                "status": "#ff9f0a"}
    return {"bg": "#ffffff", "field": "#f2f2f7", "text": "#1c1c1e", "sub": "#8e8e93",
            "owned": "#22863a", "bar": "#f2f2f7", "accent": "#007aff",
            "status": "#c76a00"}


# ====================================================================== interface
class GameChecklist(ui.View):
    def __init__(self):
        super().__init__()
        self.name = "Ma collection de jeux"
        self.theme = make_theme()
        self.background_color = self.theme["bg"]

        self.coll = Collection()
        self.prices = PriceCache()
        self.token = read_token()

        self.label = LABELS[0]       # console affichée
        self.filter_index = 0        # index dans FILTERS
        self.mode = MODE_CHECK
        self.query = ""
        self.rows = []               # [(section, jeux affichés, possédés, total)]
        self.closed = False
        self.wake = threading.Event()  # réveille le chargeur de prix
        self.busy = False            # calcul de valeur en cours
        self.loading = None          # jeu dont le prix est en cours de chargement
        self.loading_label = None
        self.last_reload = 0.0

        self.build_ui()
        try:
            NET.web = WebFetcher(self)
        except Exception:
            NET.web = None
        self.layout()
        self.refresh()
        run_thread(self.price_worker)

    # -------------------------------------------------------------- construction
    def build_ui(self):
        t = self.theme

        self.search = ui.TextField()
        self.search.placeholder = "Rechercher un jeu ou une série..."
        self.search.clear_button_mode = "while_editing"
        self.search.autocorrection_type = False
        self.search.spellchecking_type = False
        self.search.background_color = t["field"]
        self.search.text_color = t["text"]
        self.search.border_width = 0
        self.search.corner_radius = 8
        self.search.delegate = self
        self.add_subview(self.search)

        self.console_ctrl = self._segmented(LABELS, self.console_changed)
        self.filter_ctrl = self._segmented(FILTERS, self.filter_changed)
        self.mode_ctrl = self._segmented(["Mode : cocher", "Mode : infos & prix"],
                                         self.mode_changed)

        self.stats = ui.Label()
        self.stats.font = ("<System-Bold>", 13)
        self.stats.text_color = t["text"]
        self.add_subview(self.stats)

        self.status = ui.Label()
        self.status.font = ("<System>", 11)
        self.status.text_color = t["status"]
        self.add_subview(self.status)

        self.table = ui.TableView()
        self.table.data_source = self
        self.table.delegate = self
        self.table.row_height = 54
        self.table.background_color = t["bg"]
        self.add_subview(self.table)

        self.bottom = ui.View()
        self.bottom.background_color = t["bar"]
        self.add_subview(self.bottom)

        self.buttons = []
        for title, action in (("Exporter", self.export_list),
                              ("Valeur console", self.value_console),
                              ("Valeur totale", self.value_all)):
            b = ui.Button(title=title)
            b.background_color = t["accent"]
            b.tint_color = "white"
            b.corner_radius = 8
            b.font = ("<System-Bold>", 13)
            b.action = action
            self.bottom.add_subview(b)
            self.buttons.append(b)

    def _segmented(self, segments, action):
        c = ui.SegmentedControl()
        c.segments = segments
        c.selected_index = 0
        c.action = action
        self.add_subview(c)
        return c

    def layout(self):
        w, h = self.width, self.height
        y = 8
        self.search.frame = (10, y, w - 20, 34)
        y += 40
        for ctrl in (self.console_ctrl, self.filter_ctrl, self.mode_ctrl):
            ctrl.frame = (10, y, w - 20, 30)
            y += 36
        self.stats.frame = (12, y, w - 24, 18)
        y += 18
        self.status.frame = (12, y, w - 24, 16)
        y += 20
        bar_h = 60  # un peu de marge pour la barre d'accueil de l'iPhone
        self.table.frame = (0, y, w, max(0, h - y - bar_h))
        self.bottom.frame = (0, h - bar_h, w, bar_h)
        bw = (w - 40) / 3.0
        for i, b in enumerate(self.buttons):
            b.frame = (10 + i * (bw + 10), 8, bw, 36)

    def will_close(self):
        self.closed = True
        self.wake.set()
        self.prices.save()

    # -------------------------------------------------------------- état / affichage
    def set_status(self, text):
        def _set():
            self.status.text = text
        ui.delay(_set, 0)

    def update_stats(self):
        here = self.coll.count(self.label)
        total_here = len(GAMES_BY[self.label])
        owned_all = sum(self.coll.count(l) for l in LABELS)
        total_all = sum(len(GAMES_BY[l]) for l in LABELS)
        self.stats.text = "%s : %d/%d   •   Toutes consoles : %d/%d" % (
            self.label, here, total_here, owned_all, total_all)

    def pending_count(self):
        n = 0
        for l in LABELS:
            for g in self.coll.owned_games(l):
                if self.coll.manual_price(l, g) is None and \
                        not self.prices.has_price(self.prices.get(key_of(l, g))):
                    n += 1
        return n

    def default_status(self):
        mins = NET.blocked_minutes()
        if mins:
            return "PriceCharting en pause encore %d min (« Saisir mon prix » possible)" % mins
        if self.loading:
            return "Chargement du prix : %s" % self.loading
        if self.mode == MODE_INFO:
            return "Touche un jeu pour voir son prix détaillé"
        return "Touche un jeu pour le cocher / décocher"

    def refresh(self):
        owned = self.coll.owned[self.label]
        query = normalize(self.query.strip())
        flt = FILTERS[self.filter_index]
        rows = []
        for section, games in SECTIONS_BY[self.label]:
            section_hit = bool(query) and query in normalize(section)
            shown = []
            for game in games:
                is_owned = game in owned
                if flt == "À acheter" and is_owned:
                    continue
                if flt == "Possédés" and not is_owned:
                    continue
                if query and not section_hit and query not in normalize(game):
                    continue
                shown.append(game)
            if shown:
                got = sum(1 for g in games if g in owned)
                rows.append((section, shown, got, len(games)))
        self.rows = rows
        self.update_stats()
        self.status.text = self.default_status()
        self.table.reload()
        self.wake.set()

    def reload_soon(self):
        """Recharge la liste au plus toutes les 1,5 s (pendant les chargements de prix)."""
        if time.time() - self.last_reload > 1.5:
            self.last_reload = time.time()
            on_main(self.table.reload)

    def save_collection(self):
        err = self.coll.save()
        if err:
            hud("Erreur de sauvegarde : %s" % err, "error", 2.5)

    def price_line(self, label, game):
        cond = self.coll.condition(label, game)
        manual = self.coll.manual_price(label, game)
        if manual is not None:
            return "Mon prix : %s" % eur(manual)
        e = self.prices.get(key_of(label, game))
        if PriceCache.has_price(e):
            est = estimate(e, cond, self.prices.fx_quick())
            if not est:
                return "%s : pas de cote pour cette condition" % cond
            if est["max"] - est["min"] >= 1:
                return "%s : ≈ %s  (ventes %s – %s)" % (
                    cond, eur(est["mid"]), eur_short(est["min"]), eur_short(est["max"]))
            return "%s : ≈ %s" % (cond, eur(est["mid"]))
        if self.loading == game and self.loading_label == label:
            return "Chargement du prix..."
        if self.mode != MODE_INFO and not self.coll.is_owned(label, game):
            return ""
        if e and e.get("v") == CACHE_VERSION and "err" in e:
            return "Prix indisponible : %s" % e["err"][:60]
        mins = NET.blocked_minutes()
        if mins:
            return "Site en pause (%d min) – « Saisir mon prix » possible" % mins
        return "Prix en attente de chargement"

    # -------------------------------------------------------------- chargement automatique
    def next_job(self):
        """Prochain jeu à chiffrer : d'abord ceux affichés en mode infos, puis les possédés."""
        candidates = []
        if self.mode == MODE_INFO:
            candidates += [(self.label, g) for _, games, _, _ in self.rows for g in games]
        candidates += [(self.label, g) for g in self.coll.owned_games(self.label)]
        for l in LABELS:
            candidates += [(l, g) for g in self.coll.owned_games(l)]
        for l, g in candidates:
            if self.coll.manual_price(l, g) is None and \
                    self.prices.needs_fetch(key_of(l, g)):
                return l, g
        return None

    def price_worker(self):
        time.sleep(1.0)
        fx_done = False
        while not self.closed:
            if NET.blocked_minutes():
                self.set_status(self.default_status())
                self.wake.wait(60)
                self.wake.clear()
                continue
            job = self.next_job()
            if not job:
                self.wake.wait(30)
                self.wake.clear()
                continue
            if not fx_done:
                self.prices.get_fx()
                fx_done = True
            label, game = job
            key = key_of(label, game)
            self.loading, self.loading_label = game, label
            self.set_status("Chargement du prix (%s) : %s" % (label, game))
            self.reload_soon()
            try:
                self.prices.put(key, fetch_prices(
                    label, game, fixed_url=self.coll.fixed_url(label, game),
                    known_url=self.prices.known_url(key), token=read_token()))
            except Exception as ex:
                self.prices.record_error(key, str(ex))
            self.loading = self.loading_label = None
            self.prices.save()
            self.reload_soon()
            if not self.next_job():
                self.set_status("Tous les prix sont à jour (%s)" % NET.mode_text())
                on_main(self.table.reload)

    # -------------------------------------------------------------- contrôles
    def console_changed(self, sender):
        self.label = LABELS[sender.selected_index]
        self.refresh()
        self.table.content_offset = (0, 0)

    def filter_changed(self, sender):
        self.filter_index = sender.selected_index
        self.refresh()

    def mode_changed(self, sender):
        self.mode = sender.selected_index
        self.refresh()

    def textfield_did_change(self, textfield):
        self.query = textfield.text or ""
        self.refresh()

    def textfield_should_return(self, textfield):
        textfield.end_editing()
        return True

    # -------------------------------------------------------------- table
    def tableview_number_of_sections(self, tableview):
        return len(self.rows)

    def tableview_number_of_rows(self, tableview, section):
        if section >= len(self.rows):
            return 0
        return len(self.rows[section][1])

    def tableview_title_for_header(self, tableview, section):
        if section >= len(self.rows):
            return ""
        name, _, got, total = self.rows[section]
        return "%s  (%d/%d)" % (name, got, total)

    def tableview_cell_for_row(self, tableview, section, row):
        t = self.theme
        cell = ui.TableViewCell("subtitle")
        cell.background_color = t["bg"]
        try:
            game = self.rows[section][1][row]
        except IndexError:
            return cell
        owned = self.coll.is_owned(self.label, game)
        cell.text_label.text = game
        cell.text_label.font = ("<System>", 14)
        cell.text_label.number_of_lines = 1
        cell.text_label.text_color = t["owned"] if owned else t["text"]
        cell.detail_text_label.text = self.price_line(self.label, game)
        cell.detail_text_label.font = ("<System>", 12)
        cell.detail_text_label.text_color = t["sub"]
        cell.accessory_type = "checkmark" if owned else "none"
        cell.selection_style = "none"
        return cell

    def tableview_did_select(self, tableview, section, row):
        try:
            game = self.rows[section][1][row]
        except IndexError:
            return
        if self.mode == MODE_INFO:
            self.show_actions(self.label, game)
            return
        self.coll.toggle(self.label, game)
        self.save_collection()
        self.refresh()

    # -------------------------------------------------------------- menu d'un jeu
    @ui.in_background
    def show_actions(self, label, game):
        import dialogs
        cur = self.coll.condition(label, game)
        owned = self.coll.is_owned(label, game)
        has_manual = self.coll.manual_price(label, game) is not None

        actions = [
            ("Voir le prix détaillé", lambda: run_thread(self.show_price, label, game)),
            ("Décocher (je ne l'ai plus)" if owned else "Cocher (je l'ai)",
             lambda: self.toggle_from_menu(label, game)),
            ("Saisir mon prix (€)", lambda: self.ask_manual(label, game)),
        ]
        if has_manual:
            actions.append(("Effacer mon prix", lambda: self.clear_manual(label, game)))
        for c in COND:
            actions.append((("✓ " if c == cur else "    ") + "Condition : " + c,
                            (lambda c=c: self.change_condition(label, game, c))))
        q = search_name(game)
        actions += [
            ("Corriger la fiche PriceCharting", lambda: self.fix_url(label, game)),
            ("Recharger le prix", lambda: self.reload_price(label, game)),
            ("Copier le nom", lambda: self.copy_name(game)),
            ("Ouvrir PriceCharting", lambda: webbrowser.open(
                self.prices.known_url(key_of(label, game)) or search_url(label, game))),
            ("eBay.fr : ventes réalisées", lambda: webbrowser.open(
                "https://www.ebay.fr/sch/i.html?LH_Sold=1&LH_Complete=1&_nkw="
                + quote_plus("%s %s PAL" % (q, FULL_NAME[label])))),
            ("Leboncoin", lambda: webbrowser.open(
                "https://www.leboncoin.fr/recherche?text="
                + quote_plus("%s %s" % (q, FULL_NAME[label])))),
            ("Clé API PriceCharting (facultatif)", self.ask_token),
        ]
        choice = dialogs.list_dialog(game, [a[0] for a in actions])
        if not choice:
            return
        dict(actions)[choice]()

    def toggle_from_menu(self, label, game):
        now_owned = self.coll.toggle(label, game)
        self.save_collection()
        on_main(self.refresh)
        hud("Coché" if now_owned else "Décoché", "success", 0.8)

    def copy_name(self, game):
        import clipboard
        clipboard.set(game)
        hud("Nom copié", "success", 0.8)

    def ask_manual(self, label, game):
        cur = self.coll.manual_price(label, game)
        try:
            txt = console.input_alert(game, "Prix en euros (ex : 12,50)",
                                      ("%.2f" % cur).replace(".", ",") if cur is not None else "",
                                      "Enregistrer")
        except KeyboardInterrupt:
            return
        try:
            value = parse_euros(txt)
        except ValueError:
            alert("Prix invalide", "Écris un nombre positif, par exemple 12,50.")
            return
        self.coll.set_manual(label, game, value)
        self.save_collection()
        on_main(self.table.reload)
        hud("Prix enregistré", "success", 0.8)

    def clear_manual(self, label, game):
        self.coll.set_manual(label, game, None)
        self.save_collection()
        on_main(self.refresh)
        hud("Prix effacé", "success", 0.8)

    def change_condition(self, label, game, cond):
        self.coll.set_condition(label, game, cond)
        self.save_collection()
        on_main(self.table.reload)
        hud("Condition : " + cond, "success", 0.8)

    def reload_price(self, label, game):
        self.prices.forget(key_of(label, game))
        on_main(self.refresh)
        hud("Prix redemandé", "success", 0.8)

    def fix_url(self, label, game):
        e = self.prices.get(key_of(label, game)) or {}
        found = e.get("title") or "aucun"
        try:
            txt = console.input_alert(
                "Corriger la fiche",
                "Jeu trouvé : %s\n\nOuvre « Ouvrir PriceCharting », trouve le bon jeu "
                "(version PAL), copie le lien de sa page puis colle-le ici. "
                "Laisse vide pour revenir à la recherche automatique." % found,
                self.coll.fixed_url(label, game) or "", "Enregistrer")
        except KeyboardInterrupt:
            return
        txt = (txt or "").strip()
        m = re.search(r"pricecharting\.com(/game/[^\s?#]+)", txt)
        if txt and not m:
            alert("Lien invalide", "Le lien doit ressembler à :\n"
                  "https://www.pricecharting.com/game/pal-playstation-2/god-of-war")
            return
        self.coll.set_fixed_url(label, game, BASE + m.group(1) if m else None)
        self.save_collection()
        self.prices.forget(key_of(label, game))
        on_main(self.refresh)
        hud("Fiche enregistrée" if m else "Recherche automatique", "success", 0.8)

    def ask_token(self):
        try:
            txt = console.input_alert(
                "Clé API PriceCharting",
                "Facultatif : les prix fonctionnent sans clé. Clé de ton abonnement "
                "PriceCharting (page Subscription). Laisse vide pour la supprimer.",
                self.token or "", "Enregistrer")
        except KeyboardInterrupt:
            return
        txt = (txt or "").strip()
        try:
            write_token(txt)
        except OSError as e:
            alert("Erreur", str(e))
            return
        self.token = txt or None
        hud("Clé enregistrée" if txt else "Clé supprimée", "success", 0.8)
        on_main(self.refresh)

    # -------------------------------------------------------------- prix détaillé d'un jeu
    def show_price(self, label, game):
        key = key_of(label, game)
        e = self.prices.get(key)
        need = not self.prices.is_fresh(key) or (e or {}).get("partial")
        if need and not read_token():
            hud("Chargement des ventes...", "success", 1.0)
            try:
                e = fetch_prices(label, game, fixed_url=self.coll.fixed_url(label, game),
                                 known_url=self.prices.known_url(key), full=True)
                self.prices.put(key, e)
                self.prices.save()
            except Exception as ex:
                self.prices.record_error(key, str(ex))
                self.prices.save()
                old = self.prices.get(key)
                if not self.prices.has_price(old):
                    on_main(self.table.reload)
                    alert("Prix indisponible", "%s\n\n%s" % (game, ex))
                    return
                e = old
        elif need:
            try:
                e = fetch_prices(label, game, fixed_url=self.coll.fixed_url(label, game),
                                 token=read_token())
                self.prices.put(key, e)
                self.prices.save()
            except Exception as ex:
                alert("Prix indisponible", "%s\n\n%s" % (game, ex))
                return
        on_main(self.table.reload)
        fx, note = self.prices.get_fx()
        cur = self.coll.condition(label, game)
        lines = ["Fiche : %s (%s)" % (e.get("title") or "?", PC[label][1]),
                 "Mis à jour le %s" % time.strftime("%d/%m/%Y", time.localtime(e.get("ts", 0))),
                 "Taux USD→EUR : %s (%s)" % (("%.4f" % fx).replace(".", ","), note), ""]
        for c in COND:
            est = estimate(e, c, fx)
            mark = "▶ " if c == cur else ""
            if not est:
                lines.append("%s%s : pas de donnée" % (mark, c))
            elif est["n"] >= 3:
                lines.append("%s%s : ≈ %s\n   ventes récentes : %s – %s (%s)" % (
                    mark, c, eur(est["mid"]), eur(est["min"]), eur(est["max"]),
                    plural(est["n"], "vente")))
            else:
                lines.append("%s%s : ≈ %s" % (mark, c, eur(est["mid"])))
        manual = self.coll.manual_price(label, game)
        if manual is not None:
            lines += ["", "Mon prix (utilisé pour la valeur) : %s" % eur(manual)]
        if e.get("err"):
            lines += ["", "Dernière mise à jour échouée : %s" % e["err"]]
        lines += ["", "Pas le bon jeu ? Menu > « Corriger la fiche PriceCharting ».",
                  e.get("url", "")]
        alert(game, "\n".join(lines))

    # -------------------------------------------------------------- valeur de la collection
    def value_console(self, sender):
        self.compute_value(self.label)

    def value_all(self, sender):
        self.compute_value(None)

    def compute_value(self, only):
        if self.busy:
            hud("Calcul déjà en cours...", "error", 1.0)
            return
        self.busy = True
        run_thread(self._compute_value, only)

    def _compute_value(self, only):
        try:
            labels = [only] if only else list(LABELS)
            if not any(self.coll.owned_games(l) for l in labels):
                alert("Collection vide", "Coche d'abord des jeux possédés.")
                return
            report = self.build_report(labels)
            on_main(self.show_text, "Valeur de la collection", report)
        except Exception as ex:
            alert("Erreur pendant le calcul", str(ex))
        finally:
            self.busy = False

    def build_report(self, labels):
        fx, note = self.prices.get_fx()
        keys = ("min", "mid", "max")
        total = dict.fromkeys(keys, 0.0)
        lines, rows, missing = [], [], []
        n_ok = 0
        for l in labels:
            sub = dict.fromkeys(keys, 0.0)
            block = []
            for g in self.coll.owned_games(l):
                cond = self.coll.condition(l, g)
                e = self.prices.get(key_of(l, g))
                manual = self.coll.manual_price(l, g)
                if manual is not None:
                    est = {"min": manual, "max": manual, "mid": manual, "n": 0, "manual": True}
                    cond_txt = "mon prix"
                else:
                    est = estimate(e, cond, fx) if self.prices.has_price(e) else None
                    cond_txt = cond
                if not est:
                    if self.prices.has_price(e):
                        why = "pas de cote pour cette condition"
                    elif e and e.get("err"):
                        why = e["err"]
                    else:
                        why = "prix en cours de chargement, réessaie dans quelques minutes"
                    missing.append("• %s – %s [%s] : %s" % (l, g, cond, why))
                    continue
                n_ok += 1
                for k in keys:
                    sub[k] += est[k]
                    total[k] += est[k]
                if abs(est["max"] - est["min"]) >= 1:
                    detail = "%s  (ventes %s – %s)" % (eur(est["mid"]), eur_short(est["min"]),
                                                       eur_short(est["max"]))
                else:
                    detail = eur(est["mid"])
                block.append("• %s [%s] : %s" % (g, cond_txt, detail))
                rows.append([l, g, cond_txt, round(est["mid"], 2), round(est["min"], 2),
                             round(est["max"], 2), (e or {}).get("title", "") if not est["manual"] else "",
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
                            "fiche_pricecharting", "url"])
                for r in rows:
                    w.writerow([str(x).replace(".", ",") if isinstance(x, float) else x
                                for x in r])
        except OSError as e:
            csv_note = "CSV non écrit : %s" % e
        return "\n".join(head + lines + [csv_note])

    def show_text(self, title, text):
        tv = ui.TextView()
        tv.name = title
        tv.editable = False
        tv.font = ("<System>", 12)
        tv.background_color = self.theme["bg"]
        tv.text_color = self.theme["text"]
        tv.text = text
        tv.present("sheet")

    # -------------------------------------------------------------- export
    @ui.in_background
    def export_list(self, sender):
        label = self.label
        owned = self.coll.owned[label]
        lines = ["MA COLLECTION %s (%d/%d)" % (FULL_NAME[label].upper(),
                                               self.coll.count(label), len(GAMES_BY[label])), ""]
        for section, games in SECTIONS_BY[label]:
            lines.append(section)
            for game in games:
                lines.append("%s %s" % ("[x]" if game in owned else "[ ]", game))
            lines.append("")
        text = "\n".join(lines)
        try:
            import clipboard
            clipboard.set(text)
            alert("Liste copiée",
                  "La liste %s a été copiée dans le presse-papiers." % FULL_NAME[label])
        except Exception:
            alert("Liste prête",
                  "Copie impossible. La sauvegarde est dans Documents/collection_jeux.json.")


def main():
    view = GameChecklist()
    view.present("fullscreen")


if __name__ == "__main__":
    main()
