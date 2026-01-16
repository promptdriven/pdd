"""
This module defines the data structures and persistence logic for the order management system.
It utilizes SQLAlchemy to map the Order and OrderItem entities to the database, ensuring
strict schema enforcement, data integrity, and financial precision.
"""

import uuid
from decimal import Decimal
from enum import Enum as PyEnum
from datetime import datetime, timezone
from typing import List

from sqlalchemy import (
    Column, 
    String, 
    Integer, 
    Numeric, 
    DateTime, 
    ForeignKey, 
    Enum, 
    CheckConstraint
)
from sqlalchemy.orm import relationship, validates
from sqlalchemy.dialects.postgresql import UUID

# Assuming Base is imported from the central database configuration
# If this were a real environment, it would be: from src.database.config import Base
from sqlalchemy.ext.declarative import declarative_base
Base = declarative_base()

class OrderStatus(PyEnum):
    """Enumeration of valid states for an order."""
    PENDING = "PENDING"
    PROCESSING = "PROCESSING"
    SHIPPED = "SHIPPED"
    DELIVERED = "DELIVERED"
    CANCELLED = "CANCELLED"


class Order(Base):
    """
    Represents a customer order within the system.
    
    Acts as the parent entity for individual OrderItems and manages the 
    lifecycle and total financial value of the purchase.
    """
    __tablename__ = "orders"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    user_id = Column(UUID(as_uuid=True), nullable=False, index=True)
    status = Column(Enum(OrderStatus), nullable=False, default=OrderStatus.PENDING)
    total_amount = Column(Numeric(precision=10, scale=2), nullable=False, default=Decimal("0.00"))
    
    created_at = Column(DateTime, default=lambda: datetime.now(timezone.utc), nullable=False)
    updated_at = Column(
        DateTime, 
        default=lambda: datetime.now(timezone.utc), 
        onupdate=lambda: datetime.now(timezone.utc), 
        nullable=False
    )

    # Relationship: One-to-Many with OrderItem. Cascade delete ensures orphans are removed.
    items = relationship("OrderItem", back_populates="order", cascade="all, delete-orphan")

    def __init__(self, user_id: uuid.UUID, items: List["OrderItem"] = None, status: OrderStatus = OrderStatus.PENDING):
        """
        Initializes an Order with its associated items.
        
        Args:
            user_id (UUID): The unique identifier of the user placing the order.
            items (List[OrderItem]): A list of OrderItem instances to attach to the order.
            status (OrderStatus): The initial status of the order.
        """
        self.id = uuid.uuid4()
        self.user_id = user_id
        self.status = status
        self.items = items or []
        self.total_amount = self.calculate_total()

    def calculate_total(self) -> Decimal:
        """
        Aggregates the cost of all associated OrderItem records.
        
        Returns:
            Decimal: The total sum of (quantity * unit_price) for all items.
        """
        total = sum((item.unit_price * item.quantity for item in self.items), Decimal("0.00"))
        self.total_amount = total.quantize(Decimal("0.01"))
        return self.total_amount

    def update_status(self, new_status: OrderStatus):
        """
        Validates and updates the order status.
        
        Prevents invalid state transitions, such as moving a DELIVERED order back to PENDING.
        
        Args:
            new_status (OrderStatus): The target status to transition to.
            
        Raises:
            ValueError: If the transition logic is violated.
        """
        forbidden_transitions = {
            OrderStatus.DELIVERED: [OrderStatus.PENDING, OrderStatus.PROCESSING, OrderStatus.CANCELLED],
            OrderStatus.CANCELLED: [OrderStatus.SHIPPED, OrderStatus.DELIVERED, OrderStatus.PROCESSING],
        }

        if self.status in forbidden_transitions and new_status in forbidden_transitions[self.status]:
            raise ValueError(f"Invalid status transition from {self.status.value} to {new_status.value}")

        self.status = new_status


class OrderItem(Base):
    """
    Represents an individual product line item within an Order.
    
    Stores the snapshot of the price at the time of purchase to ensure 
    historical financial accuracy.
    """
    __tablename__ = "order_items"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    order_id = Column(UUID(as_uuid=True), ForeignKey("orders.id", ondelete="CASCADE"), nullable=False)
    product_id = Column(UUID(as_uuid=True), nullable=False)
    
    # Financial precision: 10 digits total, 2 after the decimal point
    quantity = Column(Integer, nullable=False)
    unit_price = Column(Numeric(precision=10, scale=2), nullable=False)

    # Relationship back to the parent order
    order = relationship("Order", back_populates="items")

    __table_args__ = (
        CheckConstraint("quantity > 0", name="check_positive_quantity"),
        CheckConstraint("unit_price >= 0", name="check_non_negative_price"),
    )

    def __init__(self, product_id: uuid.UUID, quantity: int, unit_price: Decimal):
        """
        Initializes an OrderItem.
        
        Args:
            product_id (UUID): Unique identifier of the product.
            quantity (int): Number of units (must be > 0).
            unit_price (Decimal): Price per unit at time of order.
        """
        if quantity <= 0:
            raise ValueError("Quantity must be a positive integer.")
        if unit_price < 0:
            raise ValueError("Unit price cannot be negative.")
            
        self.id = uuid.uuid4()
        self.product_id = product_id
        self.quantity = quantity
        self.unit_price = unit_price

    def __repr__(self):
        return f"<OrderItem(product_id={self.product_id}, qty={self.quantity}, price={self.unit_price})>"