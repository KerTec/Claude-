# -*- coding: utf-8 -*-
"""
Ma collection de jeux – checklist multi-consoles pour Pythonista (iPhone / iPad)

Consoles : PS2, N64, DS, 3DS, Xbox 360, Wii, GameCube, Switch.

Fichiers (dans Documents/) :
  collection_jeux.json      jeux possédés + conditions + prix saisis à la main
                            (migration automatique depuis l'ancien collection_ps2.json)
  prix_cache.json           prix PriceCharting déjà consultés (gardés 30 jours)
  pricecharting_token.txt   clé API PriceCharting (facultative)
  valeur_collection.csv     export de la valeur de la collection
  debug_pricecharting.html  dernière page non reconnue (pour diagnostic)

Prix :
  * Sans clé API : aucune requête automatique. Le site n'est interrogé que quand
    tu touches « Voir le prix » (1 requête toutes les 8 s maximum, pause d'1 h
    si le site bloque). Tu peux aussi saisir ton propre prix.
  * Avec une clé API officielle PriceCharting (abonnement payant), les prix se
    chargent automatiquement en mode « Infos & prix » et pour le calcul de la
    valeur. Clé : menu d'un jeu > « Clé API PriceCharting », ou fichier
    Documents/pricecharting_token.txt.

Utilisation :
  * Mode « Cocher » : toucher un jeu le coche / décoche.
  * Mode « Infos & prix » : toucher un jeu ouvre son menu (prix, condition,
    copier, eBay, Leboncoin...).
"""

import csv
import json
import os
import re
import threading
import time
import unicodedata
import webbrowser
from urllib.parse import quote_plus

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

CACHE_TTL = 30 * 24 * 3600  # un prix est gardé 30 jours (les cotes bougent peu)
ERR_TTL = 60 * 60           # après une erreur, pas de nouvel essai automatique avant 1 h
MIN_GAP = 8.0               # au moins 8 s entre deux requêtes vers PriceCharting
BLOCK_PAUSE = 3600          # pause d'1 h après un blocage anti-robot
DEFAULT_FX = 0.92           # taux USD→EUR de secours si hors ligne

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

# condition : (id de la cote sur la page PriceCharting, suffixe du bloc des ventes, champ API)
COND = {
    "Disque seul": ("used_price", "used", "loose-price"),
    "Complet": ("complete_price", "cib", "cib-price"),
    "Neuf": ("new_price", "new", "new-price"),
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
    """Nom à envoyer aux sites : sans parenthèses, premier titre de « X / Y », sans accents."""
    g = re.sub(r"\s*\(.*?\)", "", game).split(" / ")[0]
    g = g.replace("’", "'").replace("–", "-")
    return strip_accents(g).strip()


def eur(x):
    """1234.5 -> « 1 234,50 € »"""
    return "{:,.2f} €".format(x).replace(",", " ").replace(".", ",")


def plural(n, word):
    return "%d %s%s" % (n, word, "s" if n > 1 else "")


def parse_euros(text):
    t = (text or "").replace("€", "").replace(" ", "").replace(" ", "").replace(",", ".")
    v = float(t)
    if v < 0:
        raise ValueError("négatif")
    return round(v, 2)


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


def save_debug(html):
    try:
        with open(DEBUG_FILE, "w", encoding="utf-8") as f:
            f.write(html or "")
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
    """Jeux possédés, condition choisie par jeu et prix saisis à la main."""

    def __init__(self):
        self.lock = threading.RLock()
        self.owned = {label: set() for label in LABELS}
        self.conditions = {}
        self.manual = {}
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


# ====================================================================== réseau
class PriceError(Exception):
    pass


class PoliteHttp:
    """Une requête à la fois, MIN_GAP secondes d'écart, 1 seul nouvel essai,
    et arrêt total pendant BLOCK_PAUSE si le site bloque."""

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

    def _block(self):
        self.blocked_until = time.time() + BLOCK_PAUSE

    def get(self, url, params=None):
        import requests
        with self.lock:
            last_error = None
            for attempt in range(2):
                mins = self.blocked_minutes()
                if mins:
                    raise PriceError("PriceCharting a bloqué les requêtes : pause automatique, "
                                     "encore %d min. Utilise « Ouvrir PriceCharting » ou "
                                     "« Saisir mon prix » en attendant." % mins)
                wait = self.last_request + MIN_GAP - time.time()
                if wait > 0:
                    time.sleep(wait)
                self.last_request = time.time()
                try:
                    r = self.session().get(url, params=params, timeout=20)
                except requests.exceptions.Timeout:
                    last_error = "délai dépassé (site trop lent)"
                except requests.exceptions.RequestException:
                    last_error = "pas de connexion internet (ou site injoignable)"
                else:
                    text = r.text or ""
                    if r.status_code == 403 or "<title>Just a moment" in text:
                        save_debug(text)
                        self._block()
                        raise PriceError("PriceCharting bloque la requête (anti-robot, code %d). "
                                         "Plus aucune requête pendant 1 h. Utilise « Ouvrir "
                                         "PriceCharting » ou « Saisir mon prix »." % r.status_code)
                    if r.status_code == 429:
                        self._block()
                        raise PriceError("PriceCharting demande de ralentir (code 429). "
                                         "Pause automatique d'1 h.")
                    if r.status_code >= 500:
                        last_error = "site en panne (code %d)" % r.status_code
                    elif r.status_code != 200:
                        raise PriceError("erreur HTTP %d" % r.status_code)
                    else:
                        return r
                if attempt == 0:
                    time.sleep(10)
            raise PriceError(last_error or "échec de la connexion")


NET = PoliteHttp()

AMOUNT = r"\$\s*([\d,]+(?:\.\d{1,2})?)"
JS_PRICE = r'class="[^"]*js-price[^"]*"[^>]*>\s*' + AMOUNT


def _amount(s):
    return float(s.replace(",", ""))


def search_url(label, game):
    q = "%s %s" % (search_name(game), PC[label][1])
    return "https://www.pricecharting.com/search-products?type=prices&q=" + quote_plus(q)


def parse_game_page(html):
    """Lit une page produit PriceCharting : cotes + ventes réalisées par condition."""
    guide = {}
    for cond, (tid, _, _) in COND.items():
        m = re.search(r'<td[^>]*id="%s"[^>]*>(.*?)</td>' % tid, html, re.S)
        p = re.search(AMOUNT, m.group(1)) if m else None
        guide[cond] = _amount(p.group(1)) if p else None

    by_suffix = {v[1]: c for c, v in COND.items()}
    sales = {c: [] for c in COND}
    marks = [(m.start(), m.group(1))
             for m in re.finditer(r"completed-auctions-([a-z\-]+)", html)]
    for i, (pos, suffix) in enumerate(marks):
        cond = by_suffix.get(suffix)
        if not cond:
            continue
        end = marks[i + 1][0] if i + 1 < len(marks) else len(html)
        block = html[pos:min(end, pos + 60000)]
        found = [_amount(x) for x in re.findall(JS_PRICE, block)] or \
                [_amount(x) for x in re.findall(AMOUNT, block)]
        # Le même identifiant peut apparaître plusieurs fois (onglet + tableau) :
        # on garde le bloc le plus fourni au lieu de tout additionner.
        if len(found) > len(sales[cond]):
            sales[cond] = found

    for cond, values in sales.items():
        g = guide.get(cond)
        if g and values:  # écarte les annonces aberrantes (lots, erreurs de saisie)
            kept = [v for v in values if g / 4.0 <= v <= g * 4.0]
            sales[cond] = kept or values
    return guide, sales


def fetch_api(label, game, token):
    """API officielle PriceCharting (clé personnelle). Prix renvoyés en centimes USD."""
    _, pcname = PC[label]
    q = "%s %s" % (search_name(game), pcname)
    r = NET.get("https://www.pricecharting.com/api/products", params={"t": token, "q": q})
    try:
        data = r.json()
    except ValueError:
        raise PriceError("réponse de l'API illisible")
    if data.get("status") != "success":
        raise PriceError("API PriceCharting : %s"
                         % data.get("error-message", "erreur (clé invalide ?)"))
    products = data.get("products") or []
    p = next((x for x in products
              if (x.get("console-name") or "").lower() == pcname.lower()), None)
    if not p:
        raise PriceError("introuvable sur PriceCharting (%s)" % pcname)
    if not any(f[2] in p for f in COND.values()) and p.get("id"):
        try:
            p = NET.get("https://www.pricecharting.com/api/product",
                        params={"t": token, "id": p["id"]}).json()
        except ValueError:
            raise PriceError("réponse de l'API illisible")

    def cents(field):
        v = p.get(field)
        if isinstance(v, (int, float)) and not isinstance(v, bool) and v > 0:
            return v / 100.0
        return None

    guide = {c: cents(v[2]) for c, v in COND.items()}
    if not any(guide.values()):
        raise PriceError("pas de cote pour ce jeu")
    return {"ts": time.time(), "url": search_url(label, game), "guide": guide,
            "sales": {c: [] for c in COND}, "api": True}


def fetch_scrape(label, game):
    slug, pcname = PC[label]
    r = NET.get("https://www.pricecharting.com/search-products",
                params={"q": "%s %s" % (search_name(game), pcname), "type": "prices"})
    url, html = r.url, r.text or ""
    if "/game/%s/" % slug not in url:  # pas de redirection directe : on prend le 1er résultat
        m = re.search(r'href="(?:https://www\.pricecharting\.com)?(/game/%s/[^"?#]+)'
                      % re.escape(slug), html)
        if not m:
            save_debug(html)
            raise PriceError("introuvable sur PriceCharting (%s)" % pcname)
        url = "https://www.pricecharting.com" + m.group(1)
        html = NET.get(url).text or ""
    guide, sales = parse_game_page(html)
    if not any(guide.values()) and not any(sales.values()):
        save_debug(html)
        raise PriceError("page lue mais prix non reconnus (voir debug_pricecharting.html)")
    return {"ts": time.time(), "url": url, "guide": guide, "sales": sales}


def fetch_prices(label, game, token=None):
    if token:
        return fetch_api(label, game, token)
    return fetch_scrape(label, game)


def estimate(entry, cond, fx):
    """min / max = vraies ventes réalisées récentes ; milieu = pile entre les deux.
    Sans ventes connues : min = max = cote PriceCharting."""
    if not isinstance(entry, dict):
        return None
    guide_all = entry.get("guide")
    if not isinstance(guide_all, dict):
        return None
    sales = (entry.get("sales") or {}).get(cond) or []
    guide = guide_all.get(cond)
    if sales:
        lo, hi = min(sales), max(sales)
    elif guide:
        lo = hi = guide
    else:
        return None
    return {"min": lo * fx, "max": hi * fx, "mid": (lo + hi) / 2.0 * fx,
            "guide": guide * fx if guide else None, "n": len(sales), "manual": False}


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

    def record_error(self, key, message):
        """Garde l'ancien prix s'il existe, note seulement l'erreur."""
        now = time.time()
        with self.lock:
            old = self.get(key)
            if old and isinstance(old.get("guide"), dict):
                new = dict(old)
                new.update({"err": message, "err_ts": now})
            else:
                new = {"ts": now, "err": message, "err_ts": now}
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
        return bool(e) and isinstance(e.get("guide"), dict)

    def is_fresh(self, key):
        e = self.get(key)
        return self.has_price(e) and time.time() - e.get("ts", 0) <= CACHE_TTL

    def needs_fetch(self, key):
        e = self.get(key)
        if not e:
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
        if valid and time.time() - c.get("ts", 0) < CACHE_TTL:
            return float(c["rate"]), "taux du jour"
        try:
            import requests
            r = requests.get("https://api.frankfurter.app/latest",
                             params={"from": "USD", "to": "EUR"}, timeout=10)
            rate = float(r.json()["rates"]["EUR"])
            with self.lock:
                self.data["_fx"] = {"rate": rate, "ts": time.time()}
            self.save()
            return rate, "taux du jour"
        except Exception:
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
        self.gen = 0                 # change à chaque rafraîchissement : stoppe l'ancien chargement
        self.busy = False            # calcul de valeur en cours

        self.build_ui()
        self.layout()
        self.refresh()

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
        self.gen += 1
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

    def default_status(self):
        mins = NET.blocked_minutes()
        if mins:
            return "PriceCharting en pause encore %d min" % mins
        if self.mode == MODE_INFO:
            if self.token:
                return "Clé API active : les prix se chargent automatiquement"
            return "Sans clé API : touche un jeu > « Voir le prix »"
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
        self.start_live()

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
            if est:
                if abs(est["max"] - est["min"]) < 0.005:
                    return "%s : ≈ %s" % (cond, eur(est["mid"]))
                return "%s : ≈ %s  (min %s – max %s)" % (
                    cond, eur(est["mid"]), eur(est["min"]), eur(est["max"]))
            return "%s : pas de prix pour cette condition" % cond
        if self.mode != MODE_INFO:
            return ""
        mins = NET.blocked_minutes()
        if mins:
            return "Site en pause (%d min) – « Saisir mon prix » possible" % mins
        if e and "err" in e:
            return "Prix indisponible – touche le jeu pour réessayer"
        if self.token:
            return "Chargement du prix..."
        return "Touche le jeu > « Voir le prix »"

    # -------------------------------------------------------------- prix automatiques (clé API)
    def start_live(self):
        self.gen += 1
        self.token = read_token()
        if self.mode != MODE_INFO or self.closed or not self.token or NET.blocked_minutes():
            return
        label = self.label
        todo = []
        for _, games, _, _ in self.rows:
            for g in games:
                if g not in todo and self.coll.manual_price(label, g) is None \
                        and self.prices.needs_fetch(key_of(label, g)):
                    todo.append(g)
        if todo:
            run_thread(self.live_worker, self.gen, label, todo, self.token)

    def live_worker(self, gen, label, todo, token):
        time.sleep(0.6)  # laisse finir la saisie dans la recherche
        if gen != self.gen or self.closed:
            return
        self.prices.get_fx()
        for i, g in enumerate(todo, 1):
            if gen != self.gen or self.closed:
                return
            key = key_of(label, g)
            if not self.prices.needs_fetch(key):
                continue
            self.set_status("Prix en direct %d/%d : %s" % (i, len(todo), g))
            try:
                self.prices.put(key, fetch_prices(label, g, token))
            except Exception as ex:
                self.prices.record_error(key, str(ex))
                if NET.blocked_minutes():
                    self.prices.save()
                    on_main(self.table.reload)
                    self.set_status("PriceCharting en pause %d min" % NET.blocked_minutes())
                    return
            self.prices.save()
            if gen == self.gen:
                on_main(self.table.reload)
        if gen == self.gen and not self.closed:
            self.set_status("Prix à jour")

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
        game = self.rows[section][1][row]
        owned = self.coll.is_owned(self.label, game)
        cell = ui.TableViewCell("subtitle")
        cell.background_color = t["bg"]
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
            ("Décocher (je ne l'ai plus)" if owned else "Cocher (je l'ai)",
             lambda: self.toggle_from_menu(label, game)),
            ("Copier le nom", lambda: self.copy_name(game)),
            ("Voir le prix (min / milieu / max)", lambda: run_thread(self.show_price, label, game)),
            ("Saisir mon prix (€)", lambda: self.ask_manual(label, game)),
        ]
        if has_manual:
            actions.append(("Effacer mon prix", lambda: self.clear_manual(label, game)))
        for c in COND:
            actions.append((("✓ " if c == cur else "    ") + "Condition : " + c,
                            (lambda c=c: self.change_condition(label, game, c))))
        q = search_name(game)
        actions += [
            ("Ouvrir PriceCharting", lambda: webbrowser.open(search_url(label, game))),
            ("eBay.fr : ventes réalisées", lambda: webbrowser.open(
                "https://www.ebay.fr/sch/i.html?LH_Sold=1&LH_Complete=1&_nkw="
                + quote_plus("%s %s PAL" % (q, FULL_NAME[label])))),
            ("Leboncoin", lambda: webbrowser.open(
                "https://www.leboncoin.fr/recherche?text="
                + quote_plus("%s %s" % (q, FULL_NAME[label])))),
            ("Clé API PriceCharting", self.ask_token),
        ]
        titles = [a[0] for a in actions]
        choice = dialogs.list_dialog(game, titles)
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
        on_main(self.table.reload)
        hud("Prix effacé", "success", 0.8)

    def change_condition(self, label, game, cond):
        self.coll.set_condition(label, game, cond)
        self.save_collection()
        on_main(self.table.reload)
        hud("Condition : " + cond, "success", 0.8)

    def ask_token(self):
        try:
            txt = console.input_alert(
                "Clé API PriceCharting",
                "Clé de ton abonnement PriceCharting (page Subscription). "
                "Laisse vide pour la supprimer.", self.token or "", "Enregistrer")
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

    # -------------------------------------------------------------- prix d'un jeu
    def entry_for(self, label, game):
        """Prix en cache s'il est récent, sinon une requête (lève PriceError)."""
        key = key_of(label, game)
        if self.prices.is_fresh(key):
            return self.prices.get(key)
        try:
            e = fetch_prices(label, game, read_token())
        except Exception as ex:
            self.prices.record_error(key, str(ex))
            self.prices.save()
            raise
        self.prices.put(key, e)
        self.prices.save()
        return e

    def show_price(self, label, game):
        if not self.prices.is_fresh(key_of(label, game)):
            hud("Recherche du prix...", "success", 1.0)
            self.set_status("Recherche du prix : %s" % game)
        try:
            e = self.entry_for(label, game)
        except Exception as ex:
            on_main(self.table.reload)
            self.set_status(self.default_status())
            alert("Prix indisponible", "%s\n\n%s" % (game, ex))
            return
        on_main(self.table.reload)
        self.set_status(self.default_status())
        fx, note = self.prices.get_fx()
        cur = self.coll.condition(label, game)
        lines = ["Source : PriceCharting (%s)" % PC[label][1],
                 "Taux USD→EUR : %s (%s)" % (("%.4f" % fx).replace(".", ","), note),
                 "Mis à jour le %s" % time.strftime("%d/%m/%Y", time.localtime(e.get("ts", 0))),
                 ""]
        for c in COND:
            est = estimate(e, c, fx)
            mark = "▶ " if c == cur else ""
            if est:
                lines.append("%s%s\n   min %s • milieu %s • max %s\n   cote %s • %s" % (
                    mark, c, eur(est["min"]), eur(est["mid"]), eur(est["max"]),
                    eur(est["guide"]) if est["guide"] else "—", plural(est["n"], "vente")))
            else:
                lines.append("%s%s : pas de donnée" % (mark, c))
        manual = self.coll.manual_price(label, game)
        if manual is not None:
            lines += ["", "Mon prix (utilisé pour la valeur) : %s" % eur(manual)]
        lines += ["", e.get("url", "")]
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
            todo = [(l, g) for l in labels for g in self.coll.owned_games(l)]
            if not todo:
                alert("Collection vide", "Coche d'abord des jeux possédés.")
                return
            token = read_token()
            self.token = token
            # Sans clé API : pas de requêtes en masse (risque de blocage) ;
            # on utilise les prix déjà connus et ceux saisis à la main.
            if token:
                self.gen += 1  # coupe le chargement automatique en parallèle
                for i, (l, g) in enumerate(todo, 1):
                    if self.closed or NET.blocked_minutes():
                        break
                    key = key_of(l, g)
                    if self.coll.manual_price(l, g) is not None or not self.prices.needs_fetch(key):
                        continue
                    self.set_status("Prix %d/%d : %s" % (i, len(todo), g))
                    try:
                        self.prices.put(key, fetch_prices(l, g, token))
                    except Exception as ex:
                        self.prices.record_error(key, str(ex))
                    if i % 10 == 0:
                        self.prices.save()
                self.prices.save()
            if self.closed:
                return
            self.set_status("Calcul du rapport...")
            report = self.build_report(labels, bool(token))
            on_main(self.refresh)
            on_main(self.show_text, "Valeur de la collection", report)
        except Exception as ex:
            alert("Erreur pendant le calcul", str(ex))
        finally:
            self.busy = False

    def build_report(self, labels, has_token):
        fx, note = self.prices.get_fx()
        keys = ("min", "mid", "max", "guide")
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
                    est = {"min": manual, "max": manual, "mid": manual, "guide": None,
                           "n": 0, "manual": True}
                    cond_txt = "mon prix"
                else:
                    est = estimate(e, cond, fx)
                    cond_txt = cond
                if not est:
                    why = (e or {}).get("err") or (
                        "pas de prix pour cette condition" if PriceCache.has_price(e) else
                        "pas encore de prix : touche le jeu > « Voir le prix » "
                        "ou « Saisir mon prix »")
                    missing.append("• %s – %s [%s] : %s" % (l, g, cond, why))
                    continue
                n_ok += 1
                for k in keys:
                    v = est[k] if est[k] is not None else est["mid"]
                    sub[k] += v
                    total[k] += v
                block.append("• %s [%s]\n   min %s | milieu %s | max %s | cote %s | %s" % (
                    g, cond_txt, eur(est["min"]), eur(est["mid"]), eur(est["max"]),
                    eur(est["guide"]) if est["guide"] else "—", plural(est["n"], "vente")))
                rows.append([l, g, cond_txt, round(est["min"], 2), round(est["mid"], 2),
                             round(est["max"], 2),
                             round(est["guide"], 2) if est["guide"] else "",
                             est["n"], (e or {}).get("url", "") if not est["manual"] else ""])
            if block:
                lines.append("=== %s : %s (milieu) | min %s | max %s ===" % (
                    FULL_NAME[l], eur(sub["mid"]), eur(sub["min"]), eur(sub["max"])))
                lines += block + [""]

        head = ["VALEUR DE LA COLLECTION (PAL, source PriceCharting + mes prix)",
                time.strftime("Calculé le %d/%m/%Y à %H:%M"),
                "Taux USD→EUR %s (%s)" % (("%.4f" % fx).replace(".", ","), note), "",
                "TOTAL  min : %s" % eur(total["min"]),
                "TOTAL  milieu : %s" % eur(total["mid"]),
                "TOTAL  max : %s" % eur(total["max"]),
                "TOTAL  cote PriceCharting : %s" % eur(total["guide"]),
                "%s, %d sans prix" % (plural(n_ok, "jeu valorisé").replace("jeu valorisés", "jeux valorisés"),
                                       len(missing))]
        if not has_token:
            head.append("(Sans clé API : seuls les prix déjà consultés ou saisis sont comptés.)")
        head.append("")
        if missing:
            lines += ["=== SANS PRIX (non comptés) ==="] + missing + [""]

        csv_note = "CSV : Documents/valeur_collection.csv"
        try:
            with open(CSV_FILE, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f, delimiter=";")  # « ; » : s'ouvre directement dans Excel/Numbers FR
                w.writerow(["console", "jeu", "condition", "min_eur", "milieu_eur",
                            "max_eur", "cote_eur", "nb_ventes", "url"])
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
        self.status.text = self.default_status()

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
