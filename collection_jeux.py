# -*- coding: utf-8 -*-
# Ma collection de jeux – LANCEUR (petit fichier : touche ▶ pour lancer l'app).
# Le code de l'app est rangé à part dans Documents/.collection_jeux/ : Pythonista n'a plus
# à ouvrir un énorme fichier dans l'éditeur (ce qui pouvait le faire planter) et garde
# le code précompilé (lancement plus rapide).
APP_VERSION = "3.48 (16/11/2026)"

import importlib
import os
import sys

DOCS = os.path.expanduser("~/Documents")
APP_DIR = os.path.join(DOCS, ".collection_jeux")
APP_FILE = os.path.join(APP_DIR, "collection_jeux_app.py")
APP_URL = "https://raw.githubusercontent.com/KerTec/Claude-/main/collection_jeux_app.py"


def download_app():
    import requests
    print("Téléchargement de l'app...")
    r = requests.get(APP_URL, params={"t": os.getpid()}, timeout=60)
    r.raise_for_status()
    compile(r.text, APP_FILE, "exec")          # refuse un fichier abîmé
    os.makedirs(APP_DIR, exist_ok=True)
    with open(APP_FILE + ".tmp", "w", encoding="utf-8") as f:
        f.write(r.text)
    os.replace(APP_FILE + ".tmp", APP_FILE)
    print("App installée.")


def load_app():
    if APP_DIR not in sys.path:
        sys.path.insert(0, APP_DIR)
    if "collection_jeux_app" in sys.modules:   # Pythonista garde les modules : on recharge
        return importlib.reload(sys.modules["collection_jeux_app"])
    return importlib.import_module("collection_jeux_app")


def main():
    if not os.path.exists(APP_FILE):
        download_app()
    try:
        app = load_app()
    except SyntaxError:
        download_app()                         # fichier abîmé : on le remplace
        app = load_app()
    app.main()


if __name__ == "__main__":
    main()
