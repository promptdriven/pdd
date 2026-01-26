Role: Senior Frontend Engineer (Next.js/TypeScript Specialist)

Task: Develop the `create_order_page` module, a Next.js page component located at `app/orders/create/page.tsx`. This page is the primary interface for users to create new orders. It must handle complex form state, real-time calculations, and secure API integration.

Context:
You are building the frontend layer for an Order Management System. The backend API (Python/FastAPI) expects specific JSON structures for order creation. You have access to shared UI components and need to orchestrate them into a cohesive workflow.

Input Files (Contextual):
*   `order_api_Python.prompt` (Defines the backend API contract, specifically `OrderCreateRequest` and `OrderResponse`).
*   `order_components_TypeScriptReact.prompt` (Defines reusable UI components like `OrderList` or `OrderSummary`).

Requirements & Specifications:

1.  **Page Structure (Next.js App Router):**
    *   File path: `app/orders/create/page.tsx`.
    *   Use the `'use client'` directive as this is an interactive form.

2.  **State Management & Validation:**
    *   Use **React Hook Form** for form management.
    *   Use **Zod** for schema validation.
    *   The form state must track:
        *   `user_id` (string, required).
        *   `items`: An array of objects containing `product_id` (string), `quantity` (int, min 1), and `unit_price` (number, for frontend calculation).
    *   Implement a custom hook or utility function to calculate the `total_price` in real-time based on the `items` array. This must mirror the backend logic: `sum(item.quantity * item.unit_price)`.

3.  **User Interface:**
    *   **Product Selection:** Since a full product catalog isn't provided, implement a *mocked* product selector (a simple `<select>` dropdown with hardcoded options like "Widget A - $10", "Widget B - $20") to simulate adding items.
    *   **Item List:** Display added items in a dynamic list/grid where users can update quantities or remove items.
    *   **Summary:** Display the live calculated total price prominently.
    *   **Submission:** A "Create Order" button that is disabled while `isSubmitting` is true.

4.  **API Integration:**
    *   Function: `handleSubmit` triggered by the form.
    *   Endpoint: `POST /api/orders`.
    *   Payload: Map form data to the `OrderCreateRequest` schema (e.g., `{ user_id: "...", items: [{ product_id: "...", quantity: 1 }] }`). Note: `unit_price` is usually looked up by the backend, but send what the API requires.
    *   Headers: Include `Authorization: Bearer <token>` (Assume a helper function `getAuthToken()` exists).
    *   **Error Handling:**
        *   401: Redirect to `/login`.
        *   400: Display server-side validation errors (e.g., "Insufficient stock").
        *   500: Generic error toast.

5.  **Post-Submission:**
    *   On success, show a success toast/message.
    *   Redirect immediately to `/orders/[orderId]` using `next/navigation`'s `useRouter`.

6.  **Accessibility:**
    *   Ensure all inputs have associated `<label>` tags.
    *   Use `aria-live` regions for the total price updates and error messages.
    *   Ensure the form is navigable via keyboard.

Deliverables:

1.  **`app/orders/create/page.tsx`**: The complete component code.
2.  **Types/Interfaces**: Define TypeScript interfaces for the Form Values and the API payload within the file or a co-located `types.ts`.
3.  **Unit Tests**: A separate code block containing a Jest/React Testing Library test file (`page.test.tsx`) that verifies:
    *   Total price calculation updates when quantity changes.
    *   The API is called with the correct payload on submit.
    *   The user is redirected after success.

Implementation Constraints:
*   Use Tailwind CSS for styling (standard utility classes).
*   Assume `lucide-react` is available for icons (e.g., trash can for delete).
*   Do not use external state management libraries (Redux/Zustand) for this local page state; React Hook Form is sufficient.

Example Code Structure (Mental Model):

```tsx
'use client';

import { useForm, useFieldArray } from 'react-hook-form';
import { zodResolver } from '@hookform/resolvers/zod';
import { z } from 'zod';
// ... imports

const orderSchema = z.object({
  // ... schema definition
});

export default function CreateOrderPage() {
  const { register, control, handleSubmit, watch } = useForm({ ... });
  const { fields, append, remove } = useFieldArray({ control, name: "items" });

  // Real-time total calculation
  const currentItems = watch("items");
  const total = currentItems.reduce(...);

  const onSubmit = async (data) => {
     // API call logic
  };

  return (
    <div className="max-w-2xl mx-auto p-6">
      <h1>Create New Order</h1>
      <form onSubmit={handleSubmit(onSubmit)}>
        {/* User ID Input */}
        {/* Dynamic Item List (Field Array) */}
        {/* Total Display */}
        {/* Submit Button */}
      </form>
    </div>
  );
}