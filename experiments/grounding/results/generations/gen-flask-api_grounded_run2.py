from flask import Flask, jsonify, request, abort
import uuid

app = Flask(__name__)

# In-memory storage
items = [
    {"id": "1", "name": "Laptop", "price": 999.99},
    {"id": "2", "name": "Mouse", "price": 25.50}
]

@app.route('/items', methods=['GET'])
def get_items():
    """Returns the list of all items."""
    return jsonify(items), 200

@app.route('/items', methods=['POST'])
def create_item():
    """Creates a new item."""
    # Check if request body is JSON
    if not request.json or 'name' not in request.json or 'price' not in request.json:
        abort(400, description="Missing 'name' or 'price' in request body")

    # Create new item object
    new_item = {
        "id": str(uuid.uuid4()), # Generates a unique ID
        "name": request.json['name'],
        "price": float(request.json['price'])
    }
    
    items.append(new_item)
    return jsonify(new_item), 201

if __name__ == '__main__':
    app.run(debug=True)