# app.py

from flask import Flask, request, jsonify

app = Flask(__name__)

# ──────────────────────────────────────────────
# In-memory store & auto-increment counter
# ──────────────────────────────────────────────
items: list[dict] = []
next_id: int = 1


# ──────────────────────────────────────────────
# Helper – validate incoming item payload
# ──────────────────────────────────────────────
def validate_item(data: dict) -> list[str]:
    """Return a list of validation error messages (empty = valid)."""
    errors = []

    if not data:
        return ["Request body must be JSON."]

    # --- name ---
    if "name" not in data:
        errors.append("'name' is required.")
    elif not isinstance(data["name"], str) or not data["name"].strip():
        errors.append("'name' must be a non-empty string.")

    # --- price ---
    if "price" not in data:
        errors.append("'price' is required.")
    elif not isinstance(data["price"], (int, float)) or data["price"] < 0:
        errors.append("'price' must be a non-negative number.")

    return errors


# ──────────────────────────────────────────────
# GET /items  – retrieve all items (with optional filters)
# ──────────────────────────────────────────────
@app.route("/items", methods=["GET"])
def get_items():
    """
    Query parameters (all optional):
      • name       – case-insensitive substring search
      • min_price  – minimum price filter
      • max_price  – maximum price filter
    """
    result = items

    # Optional: filter by name substring
    name_query = request.args.get("name")
    if name_query:
        result = [i for i in result if name_query.lower() in i["name"].lower()]

    # Optional: filter by min_price
    min_price = request.args.get("min_price", type=float)
    if min_price is not None:
        result = [i for i in result if i["price"] >= min_price]

    # Optional: filter by max_price
    max_price = request.args.get("max_price", type=float)
    if max_price is not None:
        result = [i for i in result if i["price"] <= max_price]

    return jsonify({"count": len(result), "items": result}), 200


# ──────────────────────────────────────────────
# GET /items/<id>  – retrieve a single item
# ──────────────────────────────────────────────
@app.route("/items/<int:item_id>", methods=["GET"])
def get_item(item_id: int):
    item = next((i for i in items if i["id"] == item_id), None)
    if item is None:
        return jsonify({"error": f"Item with id {item_id} not found."}), 404
    return jsonify(item), 200


# ──────────────────────────────────────────────
# POST /items  – create a new item
# ──────────────────────────────────────────────
@app.route("/items", methods=["POST"])
def create_item():
    """
    Expected JSON body:
    {
        "name":  "Widget",
        "price": 9.99
    }
    """
    global next_id

    data = request.get_json(silent=True)
    errors = validate_item(data)

    if errors:
        return jsonify({"errors": errors}), 400

    new_item = {
        "id": next_id,
        "name": data["name"].strip(),
        "price": round(float(data["price"]), 2),
    }
    items.append(new_item)
    next_id += 1

    return jsonify(new_item), 201


# ──────────────────────────────────────────────
# Error handlers
# ──────────────────────────────────────────────
@app.errorhandler(404)
def not_found(e):
    return jsonify({"error": "Resource not found."}), 404


@app.errorhandler(405)
def method_not_allowed(e):
    return jsonify({"error": "Method not allowed."}), 405


# ──────────────────────────────────────────────
# Run
# ──────────────────────────────────────────────
if __name__ == "__main__":
    # Pre-seed a couple of items for quick testing
    items.extend([
        {"id": 1, "name": "Keyboard", "price": 49.99},
        {"id": 2, "name": "Mouse",    "price": 29.99},
    ])
    next_id = 3

    app.run(debug=True, port=5000)