"""
Smart DTC: Demand-Responsive Bus Booking and Surge Dispatch System
==================================================================
Python project for 2026CSAE100 Computational Thinking and Programming,
Bennett University, B.Tech. CSE 2026-2030.
Team: Ankit Verma (Team Leader), Anibirnna Satpathy, Jaahnavi Shrivastava,
      Sakshi Ojha, Muskaan Singh

HOW TO RUN  [E1]
    1. Install Python 3.9 or newer (Windows: tick "Add python.exe to PATH")
    2. Install Flask once:          pip install flask
       (Mac/Linux "externally-managed-environment" error: CODE_GUIDE.txt)
    3. Start the website:           python app.py
    4. Open the address it prints, usually http://127.0.0.1:5000
    Start again with only the sample data:   python app.py reset

THE FILES (keep them together in one folder)
    app.py          all the Python: rules, bus timetables, database,
                    every web page and the live data feed
    index.html      every page of the website and its JavaScript
    style.css       the navy and light design
    smartdtc.db     the SQLite database (made again if it is deleted)
    CODE_GUIDE.txt  plain-English explanation of this code

EXPERIENTIAL LEARNING
    Tags [E1] ... [E10] in the comments mark where each experiential lab
    is used. The Python Lab page (/python-lab) runs the same code live.
"""

import math
import os
import platform
import random
import socket
import sqlite3
import sys
import uuid
from datetime import datetime, timedelta
from functools import wraps
from importlib.metadata import version as package_version

# [E1] Check the installation first, like typing `python --version`.
if sys.version_info < (3, 9):
    print("Smart DTC needs Python 3.9 or newer. You have Python",
          platform.python_version())
    sys.exit(1)

# [E10] Flask is not part of Python itself. If it is missing, the import
# raises ImportError: we catch it and say how to fix it.
try:
    from flask import (Flask, Response, abort, flash, jsonify, redirect,
                       render_template, request, session, url_for)
except ImportError:
    print("Flask is not installed. In a terminal, run:  pip install flask")
    sys.exit(1)


# =====================================================================
# 1. SETTINGS - named constants                                    [E7]
#    A value used in several places gets a CAPITAL name, written once.
# =====================================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "smartdtc.db")
TEMPLATE_PATH = os.path.join(BASE_DIR, "index.html")
CSS_PATH = os.path.join(BASE_DIR, "style.css")

ADMIN_PASSWORD = "dtc2026"        # depot admin password (demo only)
BUS_CAPACITY = 35                 # seats in one DTC bus
SURGE_THRESHOLD = 35              # one full busload waiting -> SURGE
RISING_THRESHOLD = 25             # early warning -> RISING
PRIORITY_AGE = 70                 # senior citizens aged 70 and above
PRIORITY_CATEGORIES = ("Woman", "Differently Abled")      # a tuple
CATEGORIES = ["General", "Student", "Senior Citizen", "Woman",
              "Differently Abled"]
SEATS_PER_ROW = 4                 # window, aisle | aisle, window
NEW_TICKET_STATUS = "WAITING FOR CONDUCTOR"
MIN_SEATS = 10                    # the smallest bus the admin can add
MAX_SEATS = 80                    # the biggest (a long articulated bus)
FIRST_NEW_NUMBER = 601            # new buses are DTC-601, DTC-602, ...

# Bus timetables. There is no real GPS in a student project, so every bus
# follows a timetable: it drives stop to stop at AVERAGE_SPEED_KMH, waits
# DWELL_MINUTES at each stop, rests LAYOVER_MINUTES at the end of its route
# and drives back. Traffic can make it late (section 5).
AVERAGE_SPEED_KMH = 30            # a city bus on the expressway
DWELL_MINUTES = 1                 # time a bus waits at every stop
LAYOVER_MINUTES = 15              # rest at the end of the route
ON_TIME_CHANCE = 0.55             # chance that a stretch has no traffic
MAX_STRETCH_DELAY = 4             # most minutes lost on one stretch
MAX_TRIP_DELAY = 12               # most minutes late on one trip (less
#                                   than the layover, so the next trip
#                                   always starts on time)
EARTH_RADIUS_KM = 6371
NOIDA_CENTRE = (28.5355, 77.3910)     # for a stop with no coordinates

# Where each stop is: (latitude, longitude), from the metro station
# pages on Wikipedia. Used for the distances between stops. [E7] dict of
# tuples
STOP_COORDINATES = {
    "Bennett University": (28.450651, 77.582009),
    "Pari Chowk": (28.463276, 77.508196),
    "Knowledge Park II": (28.456956, 77.500189),
    "Sector 146": (28.468877, 77.454964),
    "Sector 142": (28.499084, 77.412611),
    "Sector 137": (28.510870, 77.403453),
    "Sector 101": (28.556402, 77.384798),
    "Botanical Garden": (28.564194, 77.334806),
    "Noida Sector 18": (28.570813, 77.326116),
    "Noida Sector 15": (28.585156, 77.311580),
    "Mayur Vihar": (28.604134, 77.289526),
    "Akshardham": (28.617911, 77.279415),
    "ITO, Delhi": (28.629371, 77.241320),
}

# Points on the road BETWEEN two stops, so a distance follows the
# expressway instead of a straight line across fields.
# [E7] The keys are tuples: (from stop, to stop).
ROUTE_VIA = {
    ("Knowledge Park II", "Sector 142"): [
        (28.448100, 77.476600), (28.468877, 77.454964),
        (28.486483, 77.432877)],
    ("Sector 142", "Botanical Garden"): [(28.510870, 77.403453)],
    ("Pari Chowk", "Sector 146"): [
        (28.456956, 77.500189), (28.448100, 77.476600),
        (28.459502, 77.465914)],
    ("Sector 146", "Sector 137"): [
        (28.486483, 77.432877), (28.494461, 77.422179),
        (28.499084, 77.412611)],
    ("Sector 137", "Sector 101"): [(28.549476, 77.389988)],
    ("Noida Sector 18", "Noida Sector 15"): [(28.578395, 77.317635)],
    ("Noida Sector 15", "Mayur Vihar"): [(28.594211, 77.294664)],
}

DEMAND_LABELS = {                 # status -> words shown on the pages
    "NORMAL": "Normal demand",
    "RISING": "Demand rising",
    "SURGE": "Surge: relief bus needed",
}

SORT_OPTIONS = {                  # [E8] a dictionary of lambda functions
    # (not in service, minutes): a tuple key puts running buses first
    "eta": lambda bus: (not bus["in_service"], bus["eta"]),
    "seats": lambda bus: -bus["available"],    # minus: most seats first
    "number": lambda bus: bus["number"],       # bus number A to Z
}

PAGE_INFO = {                     # page -> (heading, line under it)
    "home": ("Live dashboard",
             "Every Smart DTC bus, updated every few seconds."),
    "track": ("Live tracking",
              "Where your bus is, stop by stop, and whether it is late."),
    "buses": ("Buses & booking", "Compare live seats and book in seconds."),
    "book": ("Book a seat", ""),
    "ticket": ("Your digital ticket",
               "Show this ticket to the conductor when you board."),
    "about": ("About Smart DTC",
              "Why we built it, and what it has done so far."),
    "lab": ("Python Lab",
            "All ten experiential labs, running inside Smart DTC."),
    "fleet": ("Fleet overview",
              "Every bus right now: passengers, location, destination "
              "and arrival."),
    "routes": ("Manage routes",
               "Add a bus to a route, set its seats and its timetable."),
    "demand": ("Demand & surge",
               "Commuters waiting at each stop, and relief buses."),
    "error": ("Not found", "Error 404"),
}

# Sample data: lists of tuples, saved with executemany()            [E7]
# A route is the bus's stops in order, separated by "|". The last number
# is how many minutes the bus needs to reach its next stop.
SAMPLE_BUSES = [
    ("DTC-425", "Bennett University | Pari Chowk | Knowledge Park II | "
                "Sector 142 | Botanical Garden", 23, BUS_CAPACITY, 6),
    ("DTC-347", "Pari Chowk | Sector 146 | Sector 137 | Sector 101 | "
                "Noida Sector 18", 29, BUS_CAPACITY, 9),
    ("DTC-534", "Botanical Garden | Noida Sector 18 | Noida Sector 15 | "
                "Mayur Vihar | Akshardham | ITO, Delhi", 34, BUS_CAPACITY,
     4),
]
SAMPLE_STOPS = [("Bennett University", 12), ("Pari Chowk", 24),
                ("Botanical Garden", 34)]
DEFAULT_FIRST_ETA = 5             # minutes to the next stop for other buses

# One folder for everything: index.html is read from the same folder as
# this file, and style.css is sent by the stylesheet() page below.
app = Flask(__name__, template_folder=BASE_DIR, static_folder=None)
# The secret key signs the session cookie (admin login, flash messages,
# "your tickets"). Use a long random value if the site is ever put online.
app.secret_key = "smart-dtc-2026-demo-key"


# =====================================================================
# 2. DATABASE - smartdtc.db has 4 tables linked by id numbers
# =====================================================================
BUSES_TABLE = """
CREATE TABLE IF NOT EXISTS {name} (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    number          TEXT    NOT NULL UNIQUE,
    route           TEXT    NOT NULL,
    occupied        INTEGER NOT NULL,
    total           INTEGER NOT NULL,
    scheduled       INTEGER NOT NULL DEFAULT 1,
    first_departure TEXT    NOT NULL DEFAULT ''
);
"""

SCHEMA = BUSES_TABLE.format(name="buses") + """
CREATE TABLE IF NOT EXISTS stops (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,
    name    TEXT    NOT NULL UNIQUE,
    waiting INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS tickets (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    code       TEXT    NOT NULL UNIQUE,
    bus_id     INTEGER NOT NULL REFERENCES buses (id),
    name       TEXT    NOT NULL,
    age        INTEGER NOT NULL,
    category   TEXT    NOT NULL,
    priority   INTEGER NOT NULL,
    seat       INTEGER NOT NULL,
    status     TEXT    NOT NULL,
    created_at TEXT    NOT NULL
);
CREATE TABLE IF NOT EXISTS dispatches (
    id             INTEGER PRIMARY KEY AUTOINCREMENT,
    label          TEXT    NOT NULL,
    stop_id        INTEGER NOT NULL REFERENCES stops (id),
    waiting_before INTEGER NOT NULL,
    waiting_after  INTEGER NOT NULL,
    created_at     TEXT    NOT NULL
);
"""

# Tickets are always read together with their bus (JOIN on the bus id).
TICKET_QUERY = ("SELECT tickets.*, buses.number AS bus_number, buses.route "
                "FROM tickets JOIN buses ON buses.id = tickets.bus_id ")


def db():
    """Open a connection to smartdtc.db.
    row_factory = sqlite3.Row lets us read a column by name: row["seat"]."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    """Create the 4 tables if they do not exist yet, update an older
    smartdtc.db, and add the sample buses and stops the first time."""
    conn = db()
    try:
        conn.executescript(SCHEMA)
        upgrade_old_database(conn)
        if conn.execute("SELECT COUNT(*) FROM buses").fetchone()[0] == 0:
            now = datetime.now()
            rows = []
            for number, route, occupied, total, eta in SAMPLE_BUSES:
                start = first_departure_for(number, split_route(route),
                                            eta, now)
                rows.append((number, route, occupied, total, 1,
                             time_text(start)))
            conn.executemany(
                "INSERT INTO buses (number, route, occupied, total, "
                "scheduled, first_departure) VALUES (?, ?, ?, ?, ?, ?)",
                rows)
        if conn.execute("SELECT COUNT(*) FROM stops").fetchone()[0] == 0:
            conn.executemany("INSERT INTO stops (name, waiting) "
                             "VALUES (?, ?)", SAMPLE_STOPS)
        conn.commit()
    finally:
        conn.close()                 # [E10] finally runs every time


def upgrade_old_database(conn):
    """Older versions of smartdtc.db kept other bus columns (an ETA, or
    where each bus was). Build the buses table again with today's columns,
    keeping every bus, ticket and dispatch: make a new table, copy the
    buses into it, delete the old table, give the new one its name."""
    columns = []
    for row in conn.execute("PRAGMA table_info(buses)"):
        columns.append(row["name"])
    if "scheduled" in columns:       # [E6] already up to date
        return
    conn.execute(BUSES_TABLE.format(name="buses_new"))
    conn.execute("INSERT INTO buses_new (id, number, route, occupied, "
                 "total) SELECT id, number, route, occupied, total "
                 "FROM buses")
    conn.execute("DROP TABLE buses")
    conn.execute("ALTER TABLE buses_new RENAME TO buses")
    # The sample buses get today's routes and a timetable that starts now
    now = datetime.now()
    first_etas = {}
    for number, route, occupied, total, eta in SAMPLE_BUSES:
        conn.execute("UPDATE buses SET route = ? WHERE number = ?",
                     (route, number))
        first_etas[number] = eta
    rows = conn.execute("SELECT id, number, route FROM buses").fetchall()
    for row in rows:
        eta = first_etas.get(row["number"], DEFAULT_FIRST_ETA)
        start = first_departure_for(row["number"], split_route(row["route"]),
                                    eta, now)
        conn.execute("UPDATE buses SET first_departure = ? WHERE id = ?",
                     (time_text(start), row["id"]))
    conn.commit()


def reset_db():
    """`python app.py reset`: delete smartdtc.db and build a fresh one."""
    try:
        os.remove(DB_PATH)
        print("Old smartdtc.db deleted.")
    except FileNotFoundError:        # [E10] nothing to delete: fine
        print("There was no smartdtc.db yet.")
    init_db()
    print("Fresh smartdtc.db created with 3 buses and 3 stops.")


def query_all(sql, params=()):
    """Run a SELECT and return every row. Values are passed separately as
    ? marks, never pasted into the SQL text: this blocks SQL injection."""
    conn = db()
    try:
        return conn.execute(sql, params).fetchall()
    finally:
        conn.close()


def query_one(sql, params=()):
    """Return the first row of a SELECT, or None if there are no rows."""
    rows = query_all(sql, params)
    if len(rows) == 0:
        return None
    return rows[0]


def number_from(sql, params=()):
    """Return the single number from a COUNT(*) or SUM(...) query."""
    return query_one(sql, params)[0]


def run_sql(sql, params=()):
    """Run one UPDATE (or INSERT) and save it with commit()."""
    conn = db()
    try:
        conn.execute(sql, params)
        conn.commit()
    finally:
        conn.close()


# =====================================================================
# 3. RULES AND CALCULATIONS - small functions, one job each
# =====================================================================
def is_priority(age, category):
    """The priority passenger rule from our report: age 70 or above, OR the
    category is Woman or Differently Abled.
    [E2] `or` joins two questions.  [E6] `in` checks the tuple."""
    return age >= PRIORITY_AGE or category in PRIORITY_CATEGORIES


def classify_demand(waiting):
    """NORMAL, RISING or SURGE for the commuters waiting at a stop.
    [E3] An if-elif-else ladder: check the highest level first, and use >=
    so the edge counts (35 is SURGE, 34 is RISING, 24 is NORMAL)."""
    if waiting >= SURGE_THRESHOLD:
        return "SURGE"
    elif waiting >= RISING_THRESHOLD:
        return "RISING"
    else:
        return "NORMAL"


def crowd_level(available):
    """Words for how full a bus is (also picks the seat ring colour). [E3]"""
    if available == 0:
        return "Full"
    elif available <= 5:
        return "Almost full"
    elif available <= 15:
        return "Filling up"
    else:
        return "Plenty of seats"


def plural(count, word):
    """'1 seat' but '12 seats'. [E3] if/else with f-strings."""
    if count == 1:
        return f"{count} {word}"
    return f"{count} {word}s"


def seat_position(seat):
    """Where a seat is. There are 4 seats per row: window, aisle | aisle,
    window. [E2] // gives the row and % gives the place inside the row:
    seat 24 -> (24 - 1) // 4 + 1 = row 6, and 24 % 4 = 0 -> window."""
    row = (seat - 1) // SEATS_PER_ROW + 1
    if seat % SEATS_PER_ROW in (0, 1):
        return f"Row {row}, window"
    return f"Row {row}, aisle"


def clean_name(text):
    """[E4] '  kamla   DEVI ' -> 'Kamla Devi'. split() cuts at the spaces
    (dropping extra ones), join() puts single spaces back, title() fixes
    the capital letters. Methods return a NEW string: we return it."""
    return " ".join(text.split()).title()


def clean_ticket_code(text):
    """[E4] ' dtc-5b0ff42e ' -> 'DTC-5B0FF42E' (strip, then upper).
    If the passenger typed only the 8 characters, 'DTC-' is added."""
    code = text.strip().upper()
    if not code.startswith("DTC-"):
        code = "DTC-" + code
    return code


def looks_like_ticket_code(code):
    """[E4] startswith(), len(), the slice [4:] and isalnum() check the
    shape of a code: 'DTC-' followed by exactly 8 letters or digits."""
    return (code.startswith("DTC-") and len(code) == 12
            and code[4:].isalnum())


def split_route(route_text):
    """[E4][E7] 'A | B | C' -> ['A', 'B', 'C']: split on the bar, then
    strip the spaces off each piece. [E5] continue skips empty pieces."""
    stops = []
    for piece in route_text.split("|"):
        name = piece.strip()
        if name == "":
            continue
        stops.append(name)
    return stops


def route_label(stops):
    """'Bennett University → Botanical Garden': the first stop, stops[0],
    and the last stop, stops[-1] (a negative index counts from the end)."""
    return f"{stops[0]} → {stops[-1]}"


def random_code(prefix, length):
    """prefix + random hexadecimal characters, e.g. 'DTC-5B0FF42E' or
    'RELIEF-2CC1'. uuid4() is a random number; .hex writes it in hex."""
    return prefix + uuid.uuid4().hex[:length].upper()


def nice_time(iso_text):
    """'2026-11-23T23:55:10' -> '23 Nov 2026, 11:55 PM'.
    [E10] Text that is not a date is shown unchanged instead of crashing."""
    try:
        moment = datetime.fromisoformat(iso_text)
    except (TypeError, ValueError):
        return iso_text
    return moment.strftime("%d %b %Y, %I:%M %p")


def clock_time(moment):
    """A datetime -> '8:05 PM'. [E4] lstrip("0") removes a leading 0."""
    return moment.strftime("%I:%M %p").lstrip("0")


def countdown_text(seconds):
    """Seconds -> what a countdown shows: 312 -> '5:12', 4000 -> '1h 06m',
    0 -> 'Now'.  [E2] // and % split seconds into minutes and seconds."""
    seconds = int(seconds)
    if seconds <= 0:
        return "Now"
    if seconds >= 3600:
        return f"{seconds // 3600}h {seconds % 3600 // 60:02d}m"
    return f"{seconds // 60}:{seconds % 60:02d}"


def looks_like_bus_number(number):
    """[E4] 'DTC-' and then exactly 3 digits, like 'DTC-601'.
    isdigit() is True only when every character is 0 to 9."""
    return (number.startswith("DTC-") and len(number) == 7
            and number[4:].isdigit())


def late_text(minutes):
    """The delay message commuters see: 0 -> 'On time',
    1 -> 'Running late by 1 minute', 5 -> 'Running late by 5 minutes'."""
    if minutes <= 0:
        return "On time"
    return f"Running late by {plural(minutes, 'minute')}"


# =====================================================================
# 4. RECURSION                                                     [E9]
#    Every recursive function needs a base case (an answer known without
#    another call) and a smaller step that moves towards it.
# =====================================================================
def to_binary(n):
    """Decimal -> binary text (lab E9, task 5). to_binary(11) -> '1011'.
    Base case:    0 or 1 is just "0" or "1".
    Smaller step: the binary of n // 2, then the last bit n % 2."""
    if n < 2:
        return str(n)
    return to_binary(n // 2) + str(n % 2)


def ticket_pattern(code):
    """The black-and-white square pattern printed on every ticket.
    Each of the 8 characters after 'DTC-' becomes one row of 8 squares:
      '5' -> int('5', 16) = 5 -> to_binary(5) = '101' -> zfill(4) = '0101'
      -> mirrored: '0101' + '1010' = '01011010'   (1 = dark square)
    [E4] code[4:] slices off 'DTC-'; [::-1] reverses a string."""
    rows = []
    for character in code[4:]:
        bits = to_binary(int(character, 16)).zfill(4)
        rows.append(bits + bits[::-1])
    return rows


def arrival_times(first_eta, gaps):
    """Minutes until a bus reaches each stop ahead: every bus timetable is
    built with it (trip_plan() in section 5). first_eta: minutes to the
    next stop; gaps: minutes between the stops after it.
    arrival_times(6, [3, 10]) -> [6, 9, 19]
    Base case:    no gaps left -> only the next stop: [first_eta].
    Smaller step: the next stop, then the rest, starting gaps[0] later.
    The depth is the number of stops ahead: never more than a few."""
    if len(gaps) == 0:
        return [first_eta]
    return [first_eta] + arrival_times(first_eta + gaps[0], gaps[1:])


def gcd(a, b):
    """Euclid's greatest common divisor: gcd(a, b) = gcd(b, a % b), and
    gcd(a, 0) = a.  gcd(28, 35) -> gcd(35, 28) -> gcd(28, 7) -> gcd(7, 0)."""
    if b == 0:
        return a
    return gcd(b, a % b)


def simplify_fraction(top, bottom):
    """Occupancy as a fraction in lowest terms: 28 of 35 seats -> '4/5'."""
    divisor = gcd(top, bottom)
    if divisor == 0:
        return "0/0"
    return f"{top // divisor}/{bottom // divisor}"


def factorial(n):
    """n! = n x (n - 1) x ... x 1. The base case n <= 1 also catches 0.
    A route with 5 stops could be driven in 5! = 120 different orders:
    that is why a depot fixes the order instead of trying every one."""
    if n <= 1:
        return 1
    return n * factorial(n - 1)


# =====================================================================
# 5. BUS TIMETABLES AND LIVE STATUS - where every bus is, right now
#    There is no real GPS, so every bus follows a TIMETABLE. It leaves
#    its first stop at its first departure time, drives stop to stop at
#    AVERAGE_SPEED_KMH, waits DWELL_MINUTES at each stop, rests
#    LAYOVER_MINUTES at the end of its route and drives back, all day:
#    trip 0 goes forwards, trip 1 comes back, trip 2 goes forwards ...
#    Traffic makes a bus late: on each stretch of road it may lose a few
#    minutes. Everything is worked out from the clock, so the database
#    keeps only one time per bus: its first departure.
# =====================================================================
def time_text(moment):
    """A datetime -> text for the database: '2026-11-24T14:05:09'."""
    return moment.isoformat(timespec="seconds")


def parse_time(text):
    """Text from the database -> a datetime, or None if it is not a time.
    [E10] fromisoformat() raises ValueError for text like 'yesterday'."""
    try:
        return datetime.fromisoformat(text)
    except (TypeError, ValueError):
        return None


def seconds_until(moment, now):
    """Whole seconds from now until `moment`, or 0 if it has passed."""
    return max(int((moment - now).total_seconds()), 0)


def stop_point(name):
    """(latitude, longitude) of a stop. A stop missing from
    STOP_COORDINATES is put in the middle of Noida instead of crashing."""
    return STOP_COORDINATES.get(name, NOIDA_CENTRE)


def distance_km(point_a, point_b):
    """Distance between two (lat, lng) points on the Earth's surface: the
    haversine formula.  [E2] ** squares, / always gives a float.
    [E8] map() turns both numbers of a point into radians at once."""
    lat1, lng1 = map(math.radians, point_a)
    lat2, lng2 = map(math.radians, point_b)
    a = (math.sin((lat2 - lat1) / 2) ** 2
         + math.cos(lat1) * math.cos(lat2)
         * math.sin((lng2 - lng1) / 2) ** 2)
    return 2 * EARTH_RADIUS_KM * math.asin(math.sqrt(a))


def segment_points(stop_a, stop_b):
    """Every point from stop_a to stop_b: the two stops plus the road
    points between them. [E7] dictionary with tuple keys; [E4] [::-1]
    reverses the list when the bus drives the other way."""
    if (stop_a, stop_b) in ROUTE_VIA:
        via = ROUTE_VIA[(stop_a, stop_b)]
    elif (stop_b, stop_a) in ROUTE_VIA:
        via = ROUTE_VIA[(stop_b, stop_a)][::-1]
    else:
        via = []
    return [stop_point(stop_a)] + via + [stop_point(stop_b)]


def path_length_km(points):
    """Length of a path = the sum of its straight pieces.
    [E6] zip(points, points[1:]) pairs every point with the next one."""
    total = 0
    for a, b in zip(points, points[1:]):
        total = total + distance_km(a, b)
    return total


def stretch_km(stop_a, stop_b):
    """Road distance between two neighbouring stops, in km."""
    return path_length_km(segment_points(stop_a, stop_b))


def route_km(stops):
    """Length of a whole route: all its stretches added up."""
    total = 0
    for a, b in zip(stops, stops[1:]):
        total = total + stretch_km(a, b)
    return total


def drive_minutes(stop_a, stop_b):
    """Timetable minutes for one stretch: distance / speed x 60, rounded
    UP to a whole minute with math.ceil(), and never less than 1. [E2]"""
    minutes = stretch_km(stop_a, stop_b) / AVERAGE_SPEED_KMH * 60
    return max(math.ceil(minutes), 1)


def trip_plan(stops):
    """The timetable of one trip in minutes after the bus leaves its first
    stop: when it is due at every stop, e.g. [0, 15, 18, 40, 48].
    [E9] arrival_times() adds up the drives and the waits (recursion)."""
    drives = []
    for a, b in zip(stops, stops[1:]):                       # [E6]
        drives.append(drive_minutes(a, b))
    gaps = []
    for drive in drives[1:]:
        gaps.append(DWELL_MINUTES + drive)
    return [0] + arrival_times(drives[0], gaps)


def cycle_minutes(stops):
    """One trip plus the rest at the end: then the next trip starts."""
    return trip_plan(stops)[-1] + LAYOVER_MINUTES


def traffic_minutes(number, trip, stretch):
    """Minutes a bus loses in traffic on one stretch of one trip.
    random.Random(seed) makes random numbers that are always the SAME for
    the same seed, so every page and every refresh sees the same delay."""
    chance = random.Random(f"{number}/{trip}/{stretch}")
    if chance.random() < ON_TIME_CHANCE:
        return 0                     # a clear road
    return chance.randint(1, MAX_STRETCH_DELAY)


def trip_delays(number, trip, stop_count):
    """How many minutes late the bus is at each stop of one trip: the
    traffic of every stretch so far added up (a running total), never more
    than MAX_TRIP_DELAY. It always leaves its first stop on time."""
    delays = [0]
    late = 0
    for stretch in range(stop_count - 1):
        late = min(late + traffic_minutes(number, trip, stretch),
                   MAX_TRIP_DELAY)
        delays.append(late)
    return delays


def first_departure_for(number, stops, first_eta, now):
    """A first departure time for a bus that is already running: it began
    two round trips ago, and its trip number 2 puts it first_eta minutes
    from its second stop right now, traffic included. The sample buses use
    it, so they start with the ETAs in our report (6, 9 and 4 minutes)."""
    drive = drive_minutes(stops[0], stops[1]) + traffic_minutes(number, 2, 0)
    trip_2_starts = now + timedelta(minutes=first_eta - drive)
    return trip_2_starts - 2 * timedelta(minutes=cycle_minutes(stops))


def trip_timetable(number, stops, trip, start):
    """One trip: the stops in the order the bus drives them, and when it
    is due and when it is expected at each one. Even trips go forwards,
    odd trips come back. [E2] % 2 tells even from odd; [E4] [::-1]
    reverses the list; [E6] zip() pairs each planned minute with a delay."""
    if trip % 2 == 0:
        order = stops
    else:
        order = stops[::-1]
    delays = trip_delays(number, trip, len(order))
    due = []
    expected = []
    for minutes, late in zip(trip_plan(order), delays):
        due.append(start + timedelta(minutes=minutes))
        expected.append(start + timedelta(minutes=minutes + late))
    return {"trip": trip, "order": order, "start": start, "due": due,
            "expected": expected, "delays": delays}


def current_trip(number, stops, first_departure, now):
    """The trip a bus is on at `now`. Before its first departure it waits
    for trip 0. [E2] // between two time spans gives the number of whole
    cycles since the first departure. A bus that has reached the end of
    its trip rests there, so then we show its next trip."""
    cycle = timedelta(minutes=cycle_minutes(stops))
    trip = 0
    if now >= first_departure:
        trip = (now - first_departure) // cycle
    info = trip_timetable(number, stops, trip, first_departure + trip * cycle)
    if now >= info["expected"][-1]:
        trip = trip + 1
        info = trip_timetable(number, stops, trip,
                              first_departure + trip * cycle)
    return info


def where_is(info, now):
    """Where the bus is on its trip: 'waiting' at the first stop,
    'moving' between two stops, or 'at_stop' for its minute at a stop.
    Returns (mode, position, coming). position counts stops along the
    trip (1.25 = a quarter of the way from stop 1 to stop 2) and coming is
    the number of the next stop. [E5] break ends the search early."""
    expected = info["expected"]
    if now < info["start"]:
        return "waiting", 0, 1
    coming = len(expected) - 1
    for index in range(1, len(expected)):
        if now < expected[index]:
            coming = index
            break
    if coming == 1:
        leave = info["start"]
    else:
        leave = expected[coming - 1] + timedelta(minutes=DWELL_MINUTES)
    if now < leave:
        return "at_stop", coming - 1, coming
    share = (now - leave) / (expected[coming] - leave)     # [E2] a fraction
    return "moving", coming - 1 + share, coming


def timeline_rows(info, mode, coming, now):
    """One row per stop for the Live Tracking timeline: its times, how late
    the bus is there, and whether the bus has passed it, is at it, goes
    there next or later. [E6] enumerate() numbers the stops; [E3] an
    if-elif ladder picks the state."""
    order = info["order"]
    rows = []
    km = 0
    for index, name in enumerate(order):
        if index > 0:
            km = km + stretch_km(order[index - 1], name)
        if index < coming - 1 or (index == coming - 1 and mode == "moving"):
            state = "passed"
        elif index == coming - 1:
            state = "here"
        elif index == coming:
            state = "next"
        else:
            state = "later"
        if index == 0:
            leaves = info["start"]
        else:
            leaves = info["expected"][index] + timedelta(minutes=DWELL_MINUTES)
        rows.append({
            "index": index, "name": name, "state": state,
            "km": round(km, 1),
            "due": clock_time(info["due"][index]),
            "expected": clock_time(info["expected"][index]),
            "leaves": clock_time(leaves),
            "late": info["delays"][index],
            "seconds": seconds_until(info["expected"][index], now),
            "first": index == 0,
            "last": index == len(order) - 1,
        })
    return rows


def parked_status(stops):
    """A bus whose scheduling is turned off: it stays at its first stop."""
    return {
        "scheduled": False, "running": False, "mode": "parked",
        "trip": None, "order": stops, "origin": stops[0],
        "destination": stops[-1], "position": 0, "next_index": 0,
        "next_stop": stops[0], "eta_seconds": 0, "eta_text": "",
        "eta_clock": "", "due_clock": "", "late": 0,
        "late_text": "Not running",
        "status_text": "Not running: scheduling is off",
        "location_text": f"Parked at {stops[0]}",
        "leaves_seconds": 0, "arrive_seconds": 0, "arrive_clock": "",
        "arrive_due_clock": "", "arrive_late": 0, "upcoming": [],
        "rows": [],
    }


def live_status(number, stops, scheduled, first_departure, now):
    """Everything the pages show about a bus at the moment `now`: where it
    is, its next stop, when it gets there, and how late it is."""
    if not scheduled:
        return parked_status(stops)
    info = current_trip(number, stops, first_departure, now)
    mode, position, coming = where_is(info, now)
    order = info["order"]
    expected = info["expected"]
    delays = info["delays"]
    if mode == "waiting":
        leaves = clock_time(info["start"])
        if now < first_departure:
            status = f"First trip leaves {order[0]} at {leaves}"
        else:
            status = f"Waiting at {order[0]}, leaves at {leaves}"
        location = f"At {order[0]} (leaves {leaves})"
    elif mode == "at_stop":
        status = f"At {order[coming - 1]} now"
        location = f"At {order[coming - 1]}"
    else:
        status = f"On the way to {order[coming]}"
        location = f"Between {order[coming - 1]} and {order[coming]}"
    upcoming = []
    for index in range(coming, len(order)):
        upcoming.append({"index": index, "name": order[index],
                         "seconds": seconds_until(expected[index], now),
                         "late": delays[index]})
    eta_seconds = seconds_until(expected[coming], now)
    return {
        "scheduled": True, "running": now >= first_departure,
        "mode": mode, "trip": info["trip"], "order": order,
        "origin": order[0], "destination": order[-1],
        "position": round(position, 3), "next_index": coming,
        "next_stop": order[coming], "eta_seconds": eta_seconds,
        "eta_text": countdown_text(eta_seconds),
        "eta_clock": clock_time(expected[coming]),
        "due_clock": clock_time(info["due"][coming]),
        "late": delays[coming], "late_text": late_text(delays[coming]),
        "status_text": status, "location_text": location,
        "leaves_seconds": seconds_until(info["start"], now),
        "arrive_seconds": seconds_until(expected[-1], now),
        "arrive_clock": clock_time(expected[-1]),
        "arrive_due_clock": clock_time(info["due"][-1]),
        "arrive_late": delays[-1], "upcoming": upcoming,
        "rows": timeline_rows(info, mode, coming, now),
    }


# =====================================================================
# 6. CHECKING INPUT - the website must never crash on bad input    [E10]
# =====================================================================
def read_int(text, default=None):
    """Like int(), but it never crashes the website: int("abc") raises
    ValueError and int(None) raises TypeError. In both cases we return
    the default instead. Used for the admin number fields."""
    try:
        return int(text)
    except (ValueError, TypeError):
        return default


def validate_booking(name_text, age_text, category):
    """Check the booking form. Returns (name, age, category), or RAISES a
    ValueError carrying a message the passenger can understand."""
    name = clean_name(name_text)
    try:
        age = int(age_text)
    except ValueError:
        raise ValueError("Please enter a valid age (a whole number).")
    letters = name.replace(" ", "").replace(".", "").replace("'", "")
    letters = letters.replace("-", "")
    name_ok = letters.isalpha() and len(name) <= 60      # [E4]
    age_ok = 1 <= age <= 120                             # [E2] chained
    category_ok = category in CATEGORIES                 # [E6]
    if not (name_ok and age_ok and category_ok):
        raise ValueError("Please enter a name, an age between 1 and 120 "
                         "and a valid category.")
    return name, age, category


def average(numbers):
    """The average of a list, to 1 decimal place.
    [E7] A running total in a loop. [E10] For an empty list len() is 0,
    so the division raises ZeroDivisionError: then the answer is 0."""
    total = 0
    for number in numbers:
        total = total + number
    try:
        return round(total / len(numbers), 1)
    except ZeroDivisionError:
        return 0


def parse_clock(text, day):
    """'07:30' -> that day at 7:30 in the morning.
    [E10] strptime() raises ValueError for text that is not a time like
    HH:MM (and AttributeError if the field is missing): we turn both into
    our own message."""
    try:
        clock = datetime.strptime(text.strip(), "%H:%M")
    except (AttributeError, ValueError):
        raise ValueError("Please enter the first departure time, "
                         "like 07:30.")
    return day.replace(hour=clock.hour, minute=clock.minute, second=0,
                       microsecond=0)


def validate_new_bus(form, now):
    """Check the 'Add a bus to a route' form. Returns a dictionary, or
    RAISES a ValueError with a message the admin can understand."""
    number = form.get("number", "").strip().upper()          # [E4]
    pickup = form.get("pickup", "")
    dropoff = form.get("dropoff", "")
    seats = read_int(form.get("seats"))
    scheduled = form.get("scheduled") == "on"                # a checkbox
    if not looks_like_bus_number(number):
        raise ValueError("A bus number looks like DTC-601: DTC- and then "
                         "3 digits.")
    if pickup not in STOP_COORDINATES or dropoff not in STOP_COORDINATES:
        raise ValueError("Please choose a pickup and a drop-off stop.")
    if pickup == dropoff:
        raise ValueError("The pickup and the drop-off must be different "
                         "stops.")
    if seats is None or not MIN_SEATS <= seats <= MAX_SEATS:   # [E2]
        raise ValueError(f"Seats must be a whole number from {MIN_SEATS} "
                         f"to {MAX_SEATS}.")
    first = now
    if scheduled:
        first = parse_clock(form.get("first_departure", ""), now)
    return {"number": number, "pickup": pickup, "dropoff": dropoff,
            "seats": seats, "scheduled": scheduled, "first_departure": first}


# =====================================================================
# 7. DATABASE ROWS -> DICTIONARIES THAT THE PAGES SHOW
# =====================================================================
def start_of_day(now):
    """Midnight today. A bus whose saved first departure is broken starts
    from here, so it still runs instead of crashing the page."""
    return now.replace(hour=0, minute=0, second=0, microsecond=0)


def bus_view(row, now):
    """Everything the pages show about one bus at the moment `now`.
    [E2] arithmetic for the free seats and the percentage."""
    stops = split_route(row["route"])
    available = row["total"] - row["occupied"]
    crowd = crowd_level(available)
    first = parse_time(row["first_departure"])
    if first is None:
        first = start_of_day(now)
    live = live_status(row["number"], stops, bool(row["scheduled"]),
                       first, now)
    return {
        "id": row["id"],
        "number": row["number"],
        "stops": stops,
        "route_label": route_label(stops),
        "search_text": (row["number"] + " " + " ".join(stops)).lower(),
        "occupied": row["occupied"],
        "total": row["total"],
        "available": available,
        "percent": row["occupied"] * 100 // row["total"],
        "eta": math.ceil(live["eta_seconds"] / 60),  # minutes, rounded up
        "crowd": crowd,
        "crowd_class": crowd.lower().replace(" ", "-"),     # [E4]
        "in_service": live["scheduled"],             # scheduling is on
        "running": live["running"],                  # and it has started
        "first_departure": nice_time(time_text(first)),
        "km": round(route_km(stops), 1),
        "live": live,
    }


def stop_view(row):
    """Everything the pages show about one stop."""
    waiting = row["waiting"]
    status = classify_demand(waiting)
    return {
        "id": row["id"],
        "name": row["name"],
        "waiting": waiting,
        "status": status,
        "label": DEMAND_LABELS[status],
        "full_loads": waiting // SURGE_THRESHOLD,     # [E2] whole busloads
        "left_over": waiting % SURGE_THRESHOLD,       # [E2] the remainder
        "to_surge": max(SURGE_THRESHOLD - waiting, 0),
    }


def ticket_view(row):
    """Everything the ticket page shows about one ticket."""
    if row["priority"]:
        label = "PRIORITY ACCESS"
    else:
        label = "SMART TICKET"
    return {
        "code": row["code"],
        "name": row["name"],
        "age": row["age"],
        "category": row["category"],
        "priority": bool(row["priority"]),
        "label": label,
        "seat": row["seat"],
        "seat_position": seat_position(row["seat"]),
        "status": row["status"],
        "booked_at": nice_time(row["created_at"]),
        "bus_id": row["bus_id"],
        "bus_number": row["bus_number"],
        "route_label": route_label(split_route(row["route"])),
        "pattern": ticket_pattern(row["code"]),
    }


def get_all_buses():
    """All buses in id order, each at the present moment.
    [E8] map() with a lambda calls bus_view() on every row."""
    now = datetime.now()
    rows = query_all("SELECT * FROM buses ORDER BY id")
    return list(map(lambda row: bus_view(row, now), rows))


def get_bus(bus_id):
    """One bus as a dictionary, or None if that id does not exist."""
    row = query_one("SELECT * FROM buses WHERE id = ?", (bus_id,))
    if row is None:
        return None
    return bus_view(row, datetime.now())


def find_bus(buses, bus_id):
    """Find a bus in a list by its id. [E5] break: stop looking as soon
    as it is found, so the rest of the list is never checked."""
    found = None
    for bus in buses:
        if bus["id"] == bus_id:
            found = bus
            break
    return found


def get_all_stops():
    """All stops in id order, as dictionaries."""
    rows = query_all("SELECT * FROM stops ORDER BY id")
    return list(map(stop_view, rows))


def get_stop(stop_id):
    """One stop as a dictionary, or None if that id does not exist."""
    row = query_one("SELECT * FROM stops WHERE id = ?", (stop_id,))
    if row is None:
        return None
    return stop_view(row)


def get_all_tickets():
    """Every ticket with its bus number, newest first."""
    return query_all(TICKET_QUERY + "ORDER BY tickets.id DESC")


def get_recent_dispatches(limit=8):
    """The latest relief-bus dispatches, with the name of each stop."""
    return query_all(
        "SELECT dispatches.*, stops.name AS stop_name FROM dispatches "
        "JOIN stops ON stops.id = dispatches.stop_id "
        "ORDER BY dispatches.id DESC LIMIT ?", (limit,))


def bus_json(bus):
    """The live part of a bus, for the JavaScript in index.html."""
    live = bus["live"]
    return {
        "id": bus["id"], "number": bus["number"],
        "in_service": bus["in_service"], "running": bus["running"],
        "next_stop": live["next_stop"], "eta_seconds": live["eta_seconds"],
        "status_text": live["status_text"],
        "location_text": live["location_text"],
        "destination": live["destination"],
        "arrive_seconds": live["arrive_seconds"],
        "arrive_clock": live["arrive_clock"],
        "late": live["late"], "late_text": live["late_text"],
        "upcoming": live["upcoming"],
        "occupied": bus["occupied"], "total": bus["total"],
        "available": bus["available"], "percent": bus["percent"],
        "crowd": bus["crowd"], "crowd_class": bus["crowd_class"],
    }


def stop_json(stop):
    """A stop, for the JavaScript in index.html."""
    return {"id": stop["id"], "name": stop["name"],
            "waiting": stop["waiting"], "status": stop["status"],
            "label": stop["label"]}


# =====================================================================
# 8. SAVING BOOKINGS AND DISPATCHES
# =====================================================================
def code_in_use(conn, code):
    """True if a ticket with this code is already saved."""
    row = conn.execute("SELECT id FROM tickets WHERE code = ?",
                       (code,)).fetchone()
    return row is not None


def save_ticket(bus_id, name, age, category):
    """Save a ticket AND fill one seat on the bus: both happen, or neither.
    Returns the new ticket code, or None if the bus is already full.
    BEGIN IMMEDIATE locks the database during the booking, so two people
    booking at the same moment can never get the same seat."""
    conn = db()
    try:
        conn.execute("BEGIN IMMEDIATE")
        bus = conn.execute("SELECT occupied, total FROM buses WHERE id = ?",
                           (bus_id,)).fetchone()
        if bus is None or bus["occupied"] >= bus["total"]:
            conn.rollback()
            return None
        seat = bus["occupied"] + 1
        # [E5] while loop: keep making codes until we get an unused one.
        # [E2] There are 16 ** 8 = 4,294,967,296 possible codes, so a
        # repeat is very rare - but checking costs almost nothing.
        code = random_code("DTC-", 8)
        while code_in_use(conn, code):
            code = random_code("DTC-", 8)
        conn.execute(
            "INSERT INTO tickets (code, bus_id, name, age, category, "
            "priority, seat, status, created_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (code, bus_id, name, age, category,
             int(is_priority(age, category)), seat, NEW_TICKET_STATUS,
             datetime.now().isoformat(timespec="seconds")))
        # Bug found in testing (see report): without this line every
        # booking on the same bus got the same seat number.
        conn.execute("UPDATE buses SET occupied = occupied + 1 "
                     "WHERE id = ?", (bus_id,))
        conn.commit()
        return code
    finally:
        conn.close()                 # [E10] runs even after `return`


def save_dispatch(stop_id):
    """Send one relief bus to a stop that is in SURGE. Saves the dispatch
    and takes one busload (35) off the waiting count, never below 0.
    Returns (label, before, after), or None if there is no surge."""
    conn = db()
    try:
        conn.execute("BEGIN IMMEDIATE")
        stop = conn.execute("SELECT waiting FROM stops WHERE id = ?",
                            (stop_id,)).fetchone()
        if stop is None or classify_demand(stop["waiting"]) != "SURGE":
            conn.rollback()
            return None
        before = stop["waiting"]
        after = max(before - SURGE_THRESHOLD, 0)
        label = random_code("RELIEF-", 4)
        conn.execute(
            "INSERT INTO dispatches (label, stop_id, waiting_before, "
            "waiting_after, created_at) VALUES (?, ?, ?, ?, ?)",
            (label, stop_id, before, after,
             datetime.now().isoformat(timespec="seconds")))
        conn.execute("UPDATE stops SET waiting = ? WHERE id = ?",
                     (after, stop_id))
        conn.commit()
        return label, before, after
    finally:
        conn.close()


def suggest_another_bus(full_bus_id):
    """When a bus is full, find the bus arriving soonest that has a seat.
    [E8] sorted() with a lambda key puts the soonest bus first.
    [E5] continue skips buses we cannot use (full, or not running); break
    stops at the first good one, so the other buses are never checked."""
    suggestion = None
    for bus in sorted(get_all_buses(), key=lambda b: b["eta"]):
        if bus["id"] == full_bus_id:
            continue
        if bus["available"] == 0 or not bus["in_service"]:
            continue
        suggestion = bus
        break
    return suggestion


def remember_ticket(code):
    """Keep the last 5 ticket codes booked in this browser (inside the
    session cookie) so the home page can list them.
    [E6] `not in` avoids repeats; [E4] the slice [-5:] keeps the last 5."""
    codes = session.get("my_tickets", [])
    if code not in codes:
        codes.append(code)
    session["my_tickets"] = codes[-5:]


def mark_boarded(ticket_code):
    """FUTURE IMPROVEMENT (see our report): the conductor portal will scan
    the ticket's QR code and change its status to BOARDED.
    [E5] `pass` is a placeholder: a function needs at least one line."""
    pass


def save_new_bus(details, stops):
    """Add a bus to a route (Manage Routes). Returns None when it worked,
    or a message to show. [E10] The bus number is UNIQUE in the database,
    so using a number twice raises sqlite3.IntegrityError: we catch it."""
    try:
        run_sql("INSERT INTO buses (number, route, occupied, total, "
                "scheduled, first_departure) VALUES (?, ?, 0, ?, ?, ?)",
                (details["number"], " | ".join(stops), details["seats"],
                 int(details["scheduled"]),
                 time_text(details["first_departure"])))
    except sqlite3.IntegrityError:
        return (f"{details['number']} is already in use. Please choose "
                "another bus number.")
    return None


def set_scheduling(bus_id, turn_on, now):
    """Turn a bus's timetable on or off. Turned on, the bus leaves its
    first stop now; turned off, it stops running and stays parked."""
    if turn_on:
        run_sql("UPDATE buses SET scheduled = 1, first_departure = ? "
                "WHERE id = ?", (time_text(now), bus_id))
    else:
        run_sql("UPDATE buses SET scheduled = 0 WHERE id = ?", (bus_id,))


def next_bus_number(buses):
    """A free bus number for the Manage Routes form: DTC-601, DTC-602, ...
    [E5] the while loop keeps counting while the number is taken. [E6]"""
    taken = []
    for bus in buses:
        taken.append(bus["number"])
    number = FIRST_NEW_NUMBER
    while f"DTC-{number}" in taken:
        number = number + 1
    return f"DTC-{number}"


# =====================================================================
# 9. ANALYSIS - lists, dictionaries, sets and functions together   [E7]
# =====================================================================
def count_by(records, field):
    """The counting pattern: {value: how many records have that value}.
    counts.get(value, 0) gives 0 the first time a value is seen."""
    counts = {}
    for record in records:
        value = record[field]
        counts[value] = counts.get(value, 0) + 1
    return counts


def ages_by_category(tickets):
    """A dictionary of lists: category -> the ages of those passengers.
    'First time, create it': an empty list before the first append."""
    ages = {}
    for ticket in tickets:
        category = ticket["category"]
        if category not in ages:
            ages[category] = []
        ages[category].append(ticket["age"])
    return ages


def build_stop_index(buses):
    """A dictionary of sets: stop name -> numbers of the buses that stop
    there. A set keeps each bus only once. Nested loop: buses, then stops.
    The Track page uses it to show where you can change buses."""
    index = {}
    for bus in buses:
        for stop in bus["stops"]:
            if stop not in index:
                index[stop] = set()
            index[stop].add(bus["number"])
    return index


def bar_rows(counts):
    """{name: count} -> rows for a bar chart, biggest first.
    [E8] sorted() by a lambda key. [E2] width % = count * 100 // biggest."""
    biggest = max(counts.values(), default=0)
    if biggest == 0:
        biggest = 1                  # no bookings yet: every bar is empty
    rows = []
    for name, count in sorted(counts.items(), key=lambda pair: pair[1],
                              reverse=True):
        rows.append({"name": name, "count": count,
                     "width": count * 100 // biggest})
    return rows


def build_stop_network(buses):
    """[E7] A dictionary of sets: stop -> the stops right next to it on
    any bus route, in both directions. Manage Routes finds new routes in
    it. A set keeps each neighbour only once."""
    network = {}
    for bus in buses:
        for a, b in zip(bus["stops"], bus["stops"][1:]):     # [E6]
            if a not in network:
                network[a] = set()
            if b not in network:
                network[b] = set()
            network[a].add(b)
            network[b].add(a)
    return network


def find_route(network, pickup, dropoff):
    """The route with the fewest stops from pickup to drop-off, found by a
    breadth-first search: look at every stop 1 step away, then 2 steps
    away, and so on, remembering how each stop was reached. Returns the
    stops in order, or [] if there is no way there.
    [E5] while loops and break; [E6] in / not in; [E7] a dictionary."""
    came_from = {pickup: None}
    to_visit = [pickup]                # stops still to look at, in order
    while len(to_visit) > 0:
        here = to_visit.pop(0)
        if here == dropoff:
            break
        for neighbour in sorted(network.get(here, set())):
            if neighbour not in came_from:
                came_from[neighbour] = here
                to_visit.append(neighbour)
    if dropoff not in came_from:
        return []
    route = []
    stop = dropoff
    while stop is not None:            # walk back from the drop-off
        route.append(stop)
        stop = came_from[stop]
    return route[::-1]                 # [E4] reversed: pickup first


# =====================================================================
# 10. WEB PAGES FOR COMMUTERS (Flask routes)
#     Each @app.route connects a web address to the function below it.
# =====================================================================
def render_page(page, title, **data):
    """Show index.html with one page switched on. **data collects any
    other named values (buses=..., stops=...) into a dictionary.
    setdefault() fills in the heading only if the page gave none."""
    heading, subheading = PAGE_INFO.get(page, ("Smart DTC", ""))
    data.setdefault("heading", heading)
    data.setdefault("subheading", subheading)
    data.setdefault("page_data", {})
    return render_template("index.html", page=page, title=title,
                           is_admin=bool(session.get("admin")), **data)


app.add_template_filter(nice_time)   # {{ text | nice_time }} in index.html
app.add_template_global(plural)      # {{ plural(3, "seat") }} in index.html
app.add_template_global(seat_position)          # the Book page seat map
app.jinja_env.globals["SEATS_PER_ROW"] = SEATS_PER_ROW


@app.route("/style.css")
def stylesheet():
    """Send style.css to the browser (file handling with open()).
    [E10] FileNotFoundError: if the file is missing, the site still works,
    only without its colours."""
    try:
        with open(CSS_PATH, encoding="utf-8") as css_file:
            css = css_file.read()
    except FileNotFoundError:
        css = "/* style.css not found: keep it in the same folder */"
    return Response(css, mimetype="text/css",
                    headers={"Cache-Control": "no-cache"})


@app.route("/api/live")
def api_live():
    """The live data feed. The JavaScript in index.html asks for this
    every few seconds and updates the buses and countdowns on screen."""
    return jsonify({
        "time": clock_time(datetime.now()),
        "buses": list(map(bus_json, get_all_buses())),
        "stops": list(map(stop_json, get_all_stops())),
    })


@app.route("/")
def home():
    """Home: the running buses, a few totals and 'find my ticket'."""
    all_buses = get_all_buses()
    # [E8] filter() keeps only the buses whose timetable is switched on
    shown = list(filter(lambda bus: bus["in_service"], all_buses))
    running = list(filter(lambda bus: bus["running"], shown))
    on_time = list(filter(lambda bus: bus["live"]["late"] == 0, running))
    priority = number_from(
        "SELECT COUNT(*) FROM tickets WHERE age >= ? OR category IN (?, ?)",
        (PRIORITY_AGE, PRIORITY_CATEGORIES[0], PRIORITY_CATEGORIES[1]))
    return render_page(
        "home", "Home", buses=shown,
        my_tickets=session.get("my_tickets", []),
        running=len(running), on_time=len(on_time),
        free_seats=sum(map(lambda bus: bus["available"], shown)),
        priority_served=priority)


@app.route("/buses")
def buses():
    """Every bus, with a search box, 'free seats only' and sorting."""
    all_buses = get_all_buses()
    search = request.args.get("q", "").strip()               # [E4]
    sort = request.args.get("sort", "eta")
    free_only = request.args.get("free") == "1"
    shown = all_buses
    if search != "":
        words = search.lower()
        # [E8] filter() keeps the buses whose stops contain the words;
        # [E6] `in` also works on strings: "garden" in "botanical garden"
        shown = list(filter(lambda bus: words in bus["search_text"], shown))
    if free_only:
        shown = list(filter(lambda bus: bus["available"] > 0
                            and bus["in_service"], shown))
    try:
        sort_key = SORT_OPTIONS[sort]
    except KeyError:                 # [E10] e.g. /buses?sort=banana
        sort = "eta"
        sort_key = SORT_OPTIONS[sort]
    shown = sorted(shown, key=sort_key)                       # [E8]
    return render_page("buses", "Buses", buses=shown, total=len(all_buses),
                       search=search, sort=sort, free_only=free_only)


@app.route("/book/<int:bus_id>", methods=["GET", "POST"])
def book(bus_id):
    """GET shows the booking form; POST checks it and saves the ticket."""
    bus = get_bus(bus_id)
    if bus is None:                                          # [E2] is
        abort(404, description="Bus not found")
    if not bus["in_service"]:
        flash(f"{bus['number']} is not running at the moment, so it "
              "cannot be booked.", "error")
        return redirect(url_for("buses"))
    if bus["available"] <= 0:
        flash("This bus is full.", "error")
        other = suggest_another_bus(bus_id)
        if other is not None:
            flash(f"Try {other['number']}: "
                  f"{plural(other['available'], 'seat')} free, next stop "
                  f"in {other['eta']} min.", "info")
        return redirect(url_for("buses"))
    form = {"name": "", "age": "", "category": "General"}
    if request.method == "POST":
        form = request.form          # keep what was typed, in case of error
        try:
            name, age, category = validate_booking(
                form.get("name", ""), form.get("age", ""),
                form.get("category", ""))
        except ValueError as error:                          # [E10]
            flash(str(error), "error")
        else:                        # [E10] else: runs only if no error
            code = save_ticket(bus_id, name, age, category)
            if code is None:
                flash("This bus is full.", "error")
                return redirect(url_for("buses"))
            remember_ticket(code)
            flash("Booking confirmed. Have a safe journey!", "success")
            return redirect(url_for("ticket", code=code))
    return render_page("book", f"Book {bus['number']}", bus=bus, form=form,
                       categories=CATEGORIES,
                       heading=f"Book {bus['number']}",
                       subheading=bus["route_label"])


@app.route("/ticket/<code>")
def ticket(code):
    """The digital ticket, e.g. /ticket/DTC-5B0FF42E."""
    row = query_one(TICKET_QUERY + "WHERE tickets.code = ?",
                    (clean_ticket_code(code),))
    if row is None:
        abort(404, description="Ticket not found")
    return render_page("ticket", row["code"], ticket=ticket_view(row))


@app.route("/find-ticket")
def find_ticket():
    """The 'Already booked?' box on the home page."""
    code = clean_ticket_code(request.args.get("code", ""))
    if not looks_like_ticket_code(code):
        flash("A ticket code looks like DTC-5B0FF42E: DTC- and then 8 "
              "letters or numbers.", "error")
        return redirect(url_for("home"))
    if query_one("SELECT id FROM tickets WHERE code = ?", (code,)) is None:
        flash(f"No ticket found with the code {code}.", "error")
        return redirect(url_for("home"))
    return redirect(url_for("ticket", code=code))


@app.route("/track")
@app.route("/track/<int:bus_id>")
def track(bus_id=None):
    """Live Tracking, like a train-status app: every running bus on the
    left, and the chosen bus stop by stop, with its delay. The address
    /track/1?part=live sends only the part of the page that changes; the
    JavaScript asks for it every few seconds and swaps it in."""
    all_buses = get_all_buses()
    shown = list(filter(lambda bus: bus["in_service"], all_buses))
    if bus_id is None:
        bus = None
        if len(shown) > 0:
            bus = shown[0]
    else:
        bus = find_bus(all_buses, bus_id)
        if bus is None:
            abort(404, description="Bus not found")
    changes = {}
    if bus is not None:
        stop_index = build_stop_index(shown)                   # [E7]
        for name in bus["stops"]:
            # [E7] set difference: the OTHER buses that stop here
            others = stop_index.get(name, set()) - {bus["number"]}
            changes[name] = sorted(others)
    page = "track"
    if request.args.get("part") == "live":
        page = "track_live"
    return render_page(page, "Live tracking", bus=bus, buses=shown,
                       changes=changes)


def impact_numbers():
    """The numbers on the Impact tab of the About page, from the database.
    Every category and every bus starts at 0, so the charts always show
    all of them: dict.fromkeys() makes {key: 0}; update() adds the counts."""
    tickets = get_all_tickets()
    served = number_from("SELECT COUNT(*) FROM tickets")
    # The same priority rule as is_priority(), written in SQL
    priority = number_from(
        "SELECT COUNT(*) FROM tickets WHERE age >= ? OR category IN (?, ?)",
        (PRIORITY_AGE, PRIORITY_CATEGORIES[0], PRIORITY_CATEGORIES[1]))
    relief = number_from("SELECT COUNT(*) FROM dispatches")
    moved = number_from("SELECT COALESCE(SUM(waiting_before - "
                        "waiting_after), 0) FROM dispatches")
    per_category = dict.fromkeys(CATEGORIES, 0)
    per_category.update(count_by(tickets, "category"))
    bus_numbers = [row["number"] for row in
                   query_all("SELECT number FROM buses ORDER BY id")]
    per_bus = dict.fromkeys(bus_numbers, 0)
    per_bus.update(count_by(tickets, "bus_number"))
    return {"served": served, "priority": priority, "relief": relief,
            "moved": moved, "by_category": bar_rows(per_category),
            "by_bus": bar_rows(per_bus)}


@app.route("/about")
def about():
    """About Smart DTC, in two tabs: why we built it, and its impact.
    **impact_numbers() unpacks the dictionary into named values."""
    tab = request.args.get("tab", "why")
    if tab not in ("why", "impact"):                        # [E6]
        tab = "why"
    return render_page("about", "About", tab=tab, **impact_numbers())


@app.route("/impact")
def impact():
    """The Impact page now lives in the About tab: open it there."""
    return render_page("about", "About", tab="impact", **impact_numbers())


@app.errorhandler(404)
def not_found(error):
    """Any 'not found': a wrong address, bus id or ticket code."""
    if request.url_rule is None:     # the address matched no page at all
        message = "Page not found"
    else:                            # e.g. abort(404, description=...)
        message = error.description
    return render_page("error", "Not found", message=message), 404


# =====================================================================
# 11. DEPOT ADMIN (password protected)
#     The Login button at the top right opens a small login form. After
#     the right password, the menu shows the admin pages: Fleet overview,
#     Manage routes, and Demand & surge.
# =====================================================================
def admin_required(view):
    """A decorator: a function that wraps another function. Writing
    @admin_required above a page makes this login check run first.
    *args and **kwargs pass on whatever the page needs (e.g. bus_id)."""
    @wraps(view)
    def wrapper(*args, **kwargs):
        if not session.get("admin"):
            flash("Please log in as depot admin first.", "login")
            return redirect(url_for("home", login=1))
        return view(*args, **kwargs)
    return wrapper


def safe_next(address):
    """The page to go back to after a wrong password: only an address on
    this website (starting with one /), never another website. [E4]"""
    address = address.split("?")[0]
    if address.startswith("/") and not address.startswith("//"):
        return address
    return url_for("home")


@app.route("/admin", methods=["GET", "POST"])
def admin_login():
    """The login form opens from the Login button at the top right of
    every page and is sent here. A correct password saves admin = True in
    the session (a signed cookie), so the next pages know who you are.
    A wrong one goes back to the same page with the form open again."""
    if request.method == "POST":
        if request.form.get("password", "") == ADMIN_PASSWORD:
            session["admin"] = True
            flash("Welcome, depot admin. Your pages are in the menu on "
                  "the left.", "success")
            return redirect(url_for("admin_dashboard"))
        flash("Incorrect admin password.", "login")
        back = safe_next(request.form.get("next", "/"))
        return redirect(back + "?login=1")
    if session.get("admin"):
        return redirect(url_for("admin_dashboard"))
    return redirect(url_for("home", login=1))


@app.route("/admin/dashboard")
@app.route("/admin/fleet")
@admin_required
def admin_dashboard():
    """Fleet overview: how many buses are running, and for every bus the
    passengers on board, where it is, where it is going and when it gets
    there."""
    buses = get_all_buses()
    running = list(filter(lambda bus: bus["running"], buses))     # [E8]
    late = list(filter(lambda bus: bus["live"]["late"] > 0, running))
    labels = ["Buses running", "Passengers on board", "On time",
              "Running late"]
    values = [len(running), sum(map(lambda bus: bus["occupied"], running)),
              len(running) - len(late), len(late)]
    stats = {}
    for label, value in zip(labels, values):     # [E6] zip pairs them
        stats[label] = value
    # [E6] enumerate numbers the 4 newest bookings 1, 2, 3, 4
    recent = list(enumerate(get_all_tickets()[:4], start=1))
    return render_page("fleet", "Fleet overview", stats=stats, buses=buses,
                       recent=recent)


@app.route("/admin/bus/<int:bus_id>", methods=["POST"])
@admin_required
def admin_bus(bus_id):
    """Change how many passengers are on board a bus (Fleet overview)."""
    row = query_one("SELECT * FROM buses WHERE id = ?", (bus_id,))
    if row is None:
        abort(404, description="Bus not found")
    occupied = read_int(request.form.get("occupied"))
    if occupied is None:
        flash("Please enter a whole number of passengers.", "error")
        return redirect(url_for("admin_dashboard"))
    occupied = min(max(occupied, 0), row["total"])   # keep 0 ... seats
    run_sql("UPDATE buses SET occupied = ? WHERE id = ?",
            (occupied, bus_id))
    flash(f"{row['number']} updated: {occupied}/{row['total']} passengers "
          "on board.", "success")
    return redirect(url_for("admin_dashboard"))


def added_message(details, stops):
    """The message after a bus was added on Manage Routes."""
    text = (f"{details['number']} added: {route_label(stops)}, "
            f"{len(stops)} stops, {round(route_km(stops), 1)} km, "
            f"{details['seats']} seats.")
    if details["scheduled"]:
        leaves = clock_time(details["first_departure"])
        text = text + f" Its first trip leaves {stops[0]} at {leaves}."
    else:
        text = text + " Scheduling is off, so it is not running yet."
    return text


@app.route("/admin/routes", methods=["GET", "POST"])
@admin_required
def admin_routes():
    """Manage routes: add a bus to a route by choosing a pickup and a
    drop-off stop (the stops in between are found by find_route()), its
    seats, and whether it runs on a timetable. The list beside the form
    turns the timetable of any bus on or off."""
    buses = get_all_buses()
    now = datetime.now()
    form = {"number": next_bus_number(buses), "pickup": "", "dropoff": "",
            "seats": str(BUS_CAPACITY), "scheduled": "on",
            "first_departure": (now + timedelta(minutes=5)).strftime("%H:%M")}
    if request.method == "POST":
        form = request.form          # keep what was typed, in case of error
        try:
            details = validate_new_bus(form, now)
        except ValueError as error:                          # [E10]
            flash(str(error), "error")
        else:
            network = build_stop_network(buses)
            stops = find_route(network, details["pickup"],
                               details["dropoff"])
            if len(stops) < 2:
                problem = "There is no road between those two stops yet."
            else:
                problem = save_new_bus(details, stops)
            if problem is None:
                flash(added_message(details, stops), "success")
                return redirect(url_for("admin_routes"))
            flash(problem, "error")
    return render_page("routes", "Manage routes", buses=buses, form=form,
                       stop_names=sorted(STOP_COORDINATES),
                       min_seats=MIN_SEATS, max_seats=MAX_SEATS)


@app.route("/admin/routes/<int:bus_id>/schedule", methods=["POST"])
@admin_required
def admin_schedule(bus_id):
    """Turn a bus's timetable on (it leaves its first stop now) or off."""
    bus = get_bus(bus_id)
    if bus is None:
        abort(404, description="Bus not found")
    turn_on = request.form.get("turn") == "on"
    set_scheduling(bus_id, turn_on, datetime.now())
    if turn_on:
        flash(f"{bus['number']} is scheduled: it leaves {bus['stops'][0]} "
              "now.", "success")
    else:
        flash(f"{bus['number']} is not scheduled any more: it has stopped "
              "running.", "info")
    return redirect(url_for("admin_routes"))


@app.route("/admin/demand")
@admin_required
def admin_demand():
    """Demand & surge: commuters waiting at each stop, surge alerts and the
    relief buses already sent (the surge dispatch from our report)."""
    # [E8] sorted() with a lambda key: the most crowded stop first
    stops = sorted(get_all_stops(), key=lambda stop: stop["waiting"],
                   reverse=True)
    surges = list(filter(lambda stop: stop["status"] == "SURGE", stops))
    return render_page("demand", "Demand & surge", stops=stops,
                       surge_count=len(surges),
                       dispatches=get_recent_dispatches(5))


@app.route("/admin/stop/<int:stop_id>", methods=["POST"])
@admin_required
def admin_stop(stop_id):
    """Update how many commuters are waiting at a stop."""
    stop = get_stop(stop_id)
    if stop is None:
        abort(404, description="Stop not found")
    waiting = read_int(request.form.get("waiting"))
    if waiting is None:
        flash("Please enter a whole number of waiting commuters.", "error")
        return redirect(url_for("admin_demand"))
    run_sql("UPDATE stops SET waiting = ? WHERE id = ?",
            (max(waiting, 0), stop_id))
    flash("Demand updated.", "success")
    return redirect(url_for("admin_demand"))


@app.route("/admin/dispatch/<int:stop_id>", methods=["POST"])
@admin_required
def admin_dispatch(stop_id):
    """Dispatch a relief bus to a stop in SURGE."""
    stop = get_stop(stop_id)
    if stop is None:
        abort(404, description="Stop not found")
    result = save_dispatch(stop_id)
    if result is None:
        flash(f"No surge at {stop['name']}: a relief bus is not needed.",
              "info")
    else:
        label, before, after = result            # unpack the tuple
        flash(f"{label} dispatched to {stop['name']}. Waiting commuters: "
              f"{before} → {after}.", "success")
    return redirect(url_for("admin_demand"))


@app.route("/admin/logout")
def admin_logout():
    """Forget the admin login."""
    session.pop("admin", None)
    flash("You have logged out of the depot admin pages.", "success")
    return redirect(url_for("home"))


# =====================================================================
# 12. PYTHON LAB PAGE - live examples of every experiential lab
#     Each example is the Python we ran (as text) and the result it gave,
#     made with the same functions and live data as the rest of the site.
# =====================================================================
def lab_example(code_text, value, note):
    """One row of a Python Lab table. repr() shows the result the way the
    Python shell does: text in quotes, lists in [ ]."""
    return {"code": code_text, "result": repr(value), "note": note}


def booking_error(name, age, category):
    """The message validate_booking() raises for this input, if any."""
    try:
        validate_booking(name, age, category)
    except ValueError as error:
        return "ValueError: " + str(error)
    return "accepted"


def route_error(number, pickup, dropoff, seats):
    """The message validate_new_bus() raises for this input, if any."""
    form = {"number": number, "pickup": pickup, "dropoff": dropoff,
            "seats": seats}
    try:
        validate_new_bus(form, datetime.now())
    except ValueError as error:
        return "ValueError: " + str(error)
    return "accepted"


def build_python_lab():
    """Build the ten topic cards (E1-E10) of the Python Lab page."""
    buses = get_all_buses()
    stops = get_all_stops()
    tickets = get_all_tickets()
    bus = buses[0]
    busiest = max(stops, key=lambda s: s["waiting"])
    fullest = max(buses, key=lambda b: b["occupied"])
    suggestion = suggest_another_bus(fullest["id"])
    stop_index = build_stop_index(buses)
    route_a = set(buses[0]["stops"])
    route_c = set(buses[-1]["stops"])
    network = build_stop_network(buses)
    n_stops = len(bus["stops"])
    w = busiest["waiting"]
    second_stop = bus["stops"][1]

    if suggestion is None:
        suggest_code = f"suggest_another_bus({fullest['id']})"
        suggest_value = None
    else:
        suggest_code = f"suggest_another_bus({fullest['id']})['number']"
        suggest_value = suggestion["number"]

    return [
        {
            "tag": "E1",
            "title": "Python installation, IDEs and first program",
            "summary": "app.py is a script: the interpreter reads it top "
                       "to bottom. It checks the Python version and that "
                       "Flask is installed, then prints a banner in the "
                       "terminal, our 'first program'.",
            "where": "version check and Flask import at the top, "
                     "check_setup(), banner_lines(), "
                     "if __name__ == '__main__'",
            "examples": [
                lab_example("platform.python_version()",
                            platform.python_version(),
                            "the Python running this website"),
                lab_example("sys.version_info >= (3, 9)",
                            sys.version_info >= (3, 9),
                            "Flask 3.1 needs Python 3.9 or newer"),
                lab_example('package_version("flask")',
                            package_version("flask"),
                            "installed with: pip install flask"),
                lab_example("__name__", __name__,
                            "'__main__' means it was started with "
                            "python app.py"),
                lab_example("banner_lines(5000)[1]", banner_lines(5000)[1],
                            "printed with print() when the server starts"),
            ],
        },
        {
            "tag": "E2",
            "title": "Operators and expressions",
            "summary": "Arithmetic, comparison and logic operators work "
                       "out seats, surges, distances and countdowns. // "
                       "and % split the waiting crowd into full busloads "
                       "and the rest.",
            "where": "stop_view(), bus_view(), seat_position(), "
                     "distance_km(), drive_minutes(), countdown_text(), "
                     "is_priority(), validate_booking()",
            "examples": [
                lab_example(f"{w} // {SURGE_THRESHOLD}",
                            w // SURGE_THRESHOLD,
                            f"full busloads waiting at {busiest['name']}"),
                lab_example(f"{w} % {SURGE_THRESHOLD}", w % SURGE_THRESHOLD,
                            "commuters left over after those buses"),
                lab_example(f"{bus['occupied']} * 100 // {bus['total']}",
                            bus["occupied"] * 100 // bus["total"],
                            f"how full {bus['number']} is (%)"),
                lab_example("16 ** 8", 16 ** 8,
                            "possible ticket codes (8 hex characters)"),
                lab_example("1 <= 72 <= 120", 1 <= 72 <= 120,
                            "chained comparison that checks an age"),
                lab_example("countdown_text(312)", countdown_text(312),
                            "312 // 60 = 5 minutes, 312 % 60 = 12 seconds"),
                lab_example('round(distance_km(stop_point("Bennett '
                            'University"), stop_point("Pari Chowk")), 1)',
                            round(distance_km(
                                stop_point("Bennett University"),
                                stop_point("Pari Chowk")), 1),
                            "km between two stops (haversine: ** and /)"),
                lab_example('drive_minutes("Bennett University", '
                            '"Pari Chowk")',
                            drive_minutes("Bennett University",
                                          "Pari Chowk"),
                            "timetable minutes: km / 30 * 60, rounded up"),
            ],
        },
        {
            "tag": "E3",
            "title": "Module review: conditions, f-strings, testing edges",
            "summary": "if-elif-else ladders (highest level first, >= "
                       "includes the edge) classify demand. On a website "
                       "request.form plays the part of input(), and we "
                       "test the edge values from our report.",
            "where": "classify_demand(), crowd_level(), is_priority(), "
                     "plural(), late_text(), timeline_rows(), book()",
            "examples": [
                lab_example("classify_demand(24)", classify_demand(24),
                            "one below the RISING level"),
                lab_example("classify_demand(25)", classify_demand(25),
                            ">= includes the edge"),
                lab_example("classify_demand(34)", classify_demand(34),
                            "report test 5: no dispatch button yet"),
                lab_example("classify_demand(35)", classify_demand(35),
                            "one full busload waiting: relief bus"),
                lab_example('is_priority(70, "General")',
                            is_priority(70, "General"),
                            "report test 2 (boundary)"),
                lab_example('is_priority(69, "General")',
                            is_priority(69, "General"),
                            "report test 3 (boundary)"),
                lab_example('plural(1, "seat")', plural(1, "seat"),
                            "if/else + f-string, no more '1 seats'"),
                lab_example("late_text(3)", late_text(3),
                            "the delay message on Live Tracking"),
            ],
        },
        {
            "tag": "E4",
            "title": "String slicing and string methods",
            "summary": "Names, ticket codes and routes typed by people are "
                       "cleaned with strip, split, title and upper. Slices "
                       "cut codes apart. Methods return new strings, so we "
                       "always store the result.",
            "where": "clean_name(), clean_ticket_code(), "
                     "looks_like_ticket_code(), split_route(), "
                     "ticket_pattern(), clock_time()",
            "examples": [
                lab_example('clean_name("  kamla   DEVI ")',
                            clean_name("  kamla   DEVI "),
                            "a typed name, cleaned"),
                lab_example('clean_ticket_code(" dtc-5b0ff42e ")',
                            clean_ticket_code(" dtc-5b0ff42e "),
                            "strip() and upper() before comparing"),
                lab_example('looks_like_ticket_code("DTC-5B0FF42E")',
                            looks_like_ticket_code("DTC-5B0FF42E"),
                            "startswith, len, slice and isalnum"),
                lab_example('"DTC-5B0FF42E"[4:]', "DTC-5B0FF42E"[4:],
                            "slice off the DTC- prefix"),
                lab_example('"0101"[::-1]', "0101"[::-1],
                            "reverse: mirrors each row of the pattern"),
                lab_example('split_route("Pari Chowk |Sector 146|  '
                            'Sector 137 ")',
                            split_route("Pari Chowk |Sector 146|  "
                                        "Sector 137 "),
                            "messy route text cleaned into a list"),
            ],
        },
        {
            "tag": "E5",
            "title": "Loop control statements",
            "summary": "break stops a search as soon as the answer is "
                       "found, continue skips values we do not want, and "
                       "pass holds the place of code we will write later. "
                       "While loops find the route for a new bus.",
            "where": "find_bus(), suggest_another_bus(), split_route(), "
                     "where_is(), find_route(), next_bus_number(), "
                     "save_ticket(), find_free_port(), mark_boarded()",
            "examples": [
                lab_example(f"find_bus(buses, {buses[-1]['id']})['number']",
                            find_bus(buses, buses[-1]["id"])["number"],
                            "break: the search stops at the match"),
                lab_example(suggest_code, suggest_value,
                            f"{fullest['number']} is the fullest bus: "
                            "continue skips it, break stops at the first "
                            "bus with a seat"),
                lab_example('split_route("A | | B")',
                            split_route("A | | B"),
                            "continue skips the empty piece"),
                lab_example('random_code("DTC-", 8)',
                            random_code("DTC-", 8),
                            "save_ticket() repeats this in a while loop "
                            "until the code is unused"),
                lab_example('mark_boarded("DTC-5B0FF42E")',
                            mark_boarded("DTC-5B0FF42E"),
                            "pass: placeholder for the conductor portal"),
                lab_example('find_route(network, "Bennett University", '
                            '"Sector 101")',
                            find_route(network, "Bennett University",
                                       "Sector 101"),
                            "while loop + break: the route for a new bus "
                            "(Manage routes)"),
            ],
        },
        {
            "tag": "E6",
            "title": "Membership operators, enumerate() and zip()",
            "summary": "in checks categories and powers the search box; "
                       "enumerate() numbers stops and bookings; zip() "
                       "pairs stops with their minutes, and each stop "
                       "with the next one.",
            "where": "is_priority(), validate_booking(), buses(), "
                     "trip_plan(), trip_timetable(), timeline_rows(), "
                     "admin_dashboard(), remember_ticket()",
            "examples": [
                lab_example('"Woman" in PRIORITY_CATEGORIES',
                            "Woman" in PRIORITY_CATEGORIES,
                            "part of the priority rule"),
                lab_example('"Student" not in PRIORITY_CATEGORIES',
                            "Student" not in PRIORITY_CATEGORIES,
                            "students are not priority by category"),
                lab_example('"garden" in bus["search_text"]',
                            "garden" in bus["search_text"],
                            "how the search box on the Buses page works"),
                lab_example('list(enumerate(bus["stops"], start=1))[:2]',
                            list(enumerate(bus["stops"], start=1))[:2],
                            "numbered stops"),
                lab_example('list(zip(["Pari Chowk", "Sector 142"], '
                            'arrival_times(6, [9])))',
                            list(zip(["Pari Chowk", "Sector 142"],
                                     arrival_times(6, [9]))),
                            "each stop paired with its minutes"),
            ],
        },
        {
            "tag": "E7",
            "title": "Integrated collection processing",
            "summary": "Lists, dictionaries, sets and functions working "
                       "together: the counting pattern, a dictionary of "
                       "lists, a dictionary of sets, tuple keys and set "
                       "operators that find where routes meet.",
            "where": "count_by(), ages_by_category(), build_stop_index(), "
                     "build_stop_network(), STOP_COORDINATES, ROUTE_VIA, "
                     "average(), bar_rows()",
            "examples": [
                lab_example('count_by(tickets, "category")',
                            count_by(tickets, "category"),
                            "tickets of each category (counting pattern)"),
                lab_example("ages_by_category(tickets)",
                            ages_by_category(tickets),
                            "a dictionary of lists"),
                lab_example(f'sorted(stop_index["{second_stop}"])',
                            sorted(stop_index[second_stop]),
                            "a dictionary of sets: buses at a stop"),
                lab_example("sorted(route_a & route_c)",
                            sorted(route_a & route_c),
                            f"& : stops on both {buses[0]['number']} and "
                            f"{buses[-1]['number']} (change buses here)"),
                lab_example("len(route_a | route_c)", len(route_a | route_c),
                            "| : different stops on the two routes"),
                lab_example('("Sector 142", "Botanical Garden") in '
                            'ROUTE_VIA',
                            ("Sector 142", "Botanical Garden") in ROUTE_VIA,
                            "a dictionary whose keys are tuples"),
                lab_example('sorted(network["Pari Chowk"])',
                            sorted(network["Pari Chowk"]),
                            "a dictionary of sets: the stops next to "
                            "Pari Chowk"),
            ],
        },
        {
            "tag": "E8",
            "title": "Lambda functions, map() and filter()",
            "summary": "Small lambda functions sort buses by a rule, keep "
                       "the buses with free seats and find the busiest "
                       "stop. map() turns every database row into a bus "
                       "and points into radians.",
            "where": "SORT_OPTIONS, buses(), suggest_another_bus(), "
                     "get_all_buses(), distance_km(), home(), "
                     "admin_dashboard(), admin_demand(), bar_rows()",
            "examples": [
                lab_example('list(map(lambda b: b["number"], '
                            'sorted(buses, key=lambda b: b["eta"])))',
                            list(map(lambda b: b["number"],
                                     sorted(buses, key=lambda b: b["eta"]))),
                            "Buses page sorted by 'arriving soonest'"),
                lab_example('list(map(lambda b: b["number"], '
                            'filter(lambda b: b["available"] > 0, buses)))',
                            list(map(lambda b: b["number"],
                                     filter(lambda b: b["available"] > 0,
                                            buses))),
                            "'only buses with free seats'"),
                lab_example('max(stops, key=lambda s: s["waiting"])["name"]',
                            busiest["name"], "the busiest stop right now"),
                lab_example('list(map(lambda s: s["status"], stops))',
                            list(map(lambda s: s["status"], stops)),
                            "the demand status of every stop"),
                lab_example('average(list(map(lambda t: t["age"], '
                            'tickets)))',
                            average(list(map(lambda t: t["age"], tickets))),
                            "average passenger age (0 if no tickets yet)"),
            ],
        },
        {
            "tag": "E9",
            "title": "Problem solving using recursion",
            "summary": "Recursive to_binary() draws the pattern on every "
                       "ticket, arrival_times() builds every bus "
                       "timetable, and Euclid's gcd() simplifies "
                       "fractions. Each has a base case and a smaller step.",
            "where": "to_binary(), ticket_pattern(), arrival_times(), "
                     "trip_plan(), gcd(), simplify_fraction(), factorial()",
            "examples": [
                lab_example("to_binary(11)", to_binary(11),
                            "base case n < 2, smaller step n // 2"),
                lab_example('ticket_pattern("DTC-5B0FF42E")[0]',
                            ticket_pattern("DTC-5B0FF42E")[0],
                            "first row of a ticket pattern: '5' -> 0101, "
                            "mirrored"),
                lab_example("arrival_times(6, [3, 10])",
                            arrival_times(6, [3, 10]),
                            "minutes to the next stops: 6, 6+3, 6+3+10"),
                lab_example('trip_plan(bus["stops"])',
                            trip_plan(bus["stops"]),
                            f"the timetable of {bus['number']}: minutes "
                            "after it leaves its first stop"),
                lab_example("gcd(28, 35)", gcd(28, 35),
                            "gcd(35, 28) -> gcd(28, 7) -> gcd(7, 0)"),
                lab_example("simplify_fraction(28, 35)",
                            simplify_fraction(28, 35),
                            "28 of 35 seats taken = 4/5 of the bus"),
                lab_example(f"factorial({n_stops})", factorial(n_stops),
                            f"orders in which {n_stops} stops could be "
                            "driven: why routes are fixed"),
                lab_example("sys.getrecursionlimit()",
                            sys.getrecursionlimit(),
                            "how deep recursion may go"),
            ],
        },
        {
            "tag": "E10",
            "title": "Exception handling and robust programming",
            "summary": "try, except, else and finally keep the website "
                       "running when input is wrong, a list is empty, a "
                       "saved time is broken or a file is missing; raise "
                       "sends our own error message.",
            "where": "read_int(), validate_booking(), validate_new_bus(), "
                     "parse_clock(), save_new_bus(), book(), average(), "
                     "parse_time(), stylesheet(), buses(), reset_db(), "
                     "find_free_port(), every conn.close()",
            "examples": [
                lab_example('read_int("72")', read_int("72"),
                            "a normal whole number"),
                lab_example('read_int("abc", 0)', read_int("abc", 0),
                            "ValueError caught: admin forms never crash"),
                lab_example('booking_error("Rahul", "abc", "General")',
                            booking_error("Rahul", "abc", "General"),
                            "report test 12"),
                lab_example('booking_error("", "200", "General")',
                            booking_error("", "200", "General"),
                            "report test 13: our own raise ValueError"),
                lab_example("average([])", average([]),
                            "ZeroDivisionError caught"),
                lab_example('parse_time("yesterday")',
                            parse_time("yesterday"),
                            "a broken saved time: no crash, the bus runs "
                            "from midnight"),
                lab_example('route_error("DTC-6", "Pari Chowk", '
                            '"Pari Chowk", "35")',
                            route_error("DTC-6", "Pari Chowk", "Pari Chowk",
                                        "35"),
                            "Manage routes: our own raise ValueError"),
            ],
        },
    ]


@app.route("/python-lab")
def python_lab():
    """Live examples of all ten experiential labs (for our teacher)."""
    all_buses = get_all_buses()
    topics = build_python_lab()
    tags = list(map(lambda topic: topic["tag"], topics))     # [E8]
    active = request.args.get("topic", "E1")
    if active not in tags:                                   # [E6]
        active = "E1"
    return render_page("lab", "Python Lab", topics=topics,
                       active_topic=active,
                       first_bus=all_buses[0]["number"],
                       last_bus=all_buses[-1]["number"])


# =====================================================================
# 13. STARTING THE PROGRAM                                         [E1]
# =====================================================================
def banner_lines(port):
    """The lines printed in the terminal when the server starts."""
    return [
        "=" * 62,
        "  Hello, Bennett! Smart DTC is running on Python "
        + platform.python_version(),
        f"  Open this address in your browser:  http://127.0.0.1:{port}",
        f"  Depot admin password:  {ADMIN_PASSWORD}",
        "  Stop the server with CTRL + C",
        "=" * 62,
    ]


def check_setup():
    """[E1] Like checking `python --version` after installing: make sure
    the other files sit in the same folder as app.py."""
    print("Checking the project files...")
    for filename in ["index.html", "style.css"]:
        if os.path.exists(os.path.join(BASE_DIR, filename)):
            print("  [OK]      " + filename)
        else:
            print("  [MISSING] " + filename + " - put it next to app.py")
    return os.path.exists(TEMPLATE_PATH)


def find_free_port(first_port=5000):
    """Try ports 5000, 5001, ... and return the first free one (on a Mac
    the AirPlay Receiver often uses port 5000).
    [E10] try / except / else / finally.  [E5] continue."""
    for port in range(first_port, first_port + 10):
        test_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            test_socket.bind(("127.0.0.1", port))
        except OSError:
            continue                  # busy: try the next port
        else:
            return port               # free: use it
        finally:
            test_socket.close()       # runs before continue AND return
    return first_port


# Python reads this file from top to bottom [E1], so by the time it gets
# here every function exists, and the database is made ready before any
# page can be opened.
init_db()

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "reset":
        reset_db()
    if not check_setup():
        print("index.html is needed to show the pages. Put it next to "
              "app.py and run again.")
        sys.exit(1)
    chosen_port = find_free_port()
    for line in banner_lines(chosen_port):
        print(line)
    app.run(host="127.0.0.1", port=chosen_port, debug=False, threaded=True)
