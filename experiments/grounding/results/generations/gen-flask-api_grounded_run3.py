from flask import Flask, jsonify, request

app = Flask(__name__)

# In-memory storage for items
items = []

@app.route('/items', methods=['GET'])
def get_items():
    """Returns a list of all items."""
    return jsonify(items), 200

@app.route('/items', methods=['POST'])
def create_item():
    """Creates a new item with id, name, and price."""
    data = request.get_json()
    
    # Basic validation
    if not all(k in data for k in ("id", "name", "price")):
        return jsonify({"error": "Missing required fields"}), 400
    
    new_item = {
        "id": data["id"],
        "name": data["name"],
        "price": data["price"]
    }
    
    items.append(new_item)
    return jsonify(new_item), 201

if __name__ == '__main__':
    app.run(debug=True)